Specialization:
---------------

TODO:

- Should I use a Map for the specd "list"?

XMPEG programs, emerging from the type checker, make reference to specific
instances of polymorphic/overloaded functions using (ELetVar t) values, where
t itself is a Inst triple of the form (Inst i ts es), i is the name of the
variable being defined, and ts/es are lists of type and evidence expressions.
The purpose of specialization is to eliminate calls to polymorphic functions
by generating a new, specialized version of the code for i for each distinct
combination of ts and es that is required in a particular program.

> {-# LANGUAGE NamedFieldPuns, FlexibleInstances, OverloadedStrings, ScopedTypeVariables #-}
> module Specializer (specializeProgram, doTrace) where

> import Common
> import Control.Monad.State
> import Data.List(intersperse, intercalate, nub, partition)
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe
> import Printer.Common hiding (empty)
> import Printer.Specialized
> import Solver (entails, SolverEnv)
> import qualified Syntax.LambdaCase as LC
> import Syntax.Specialized hiding (Defn(..))
> import qualified Syntax.Specialized as X
> import qualified Syntax.XMPEG.TSubst as T
> import Syntax.XMPEG.TSubst hiding (extend)

> import qualified Debug.Trace as Trace
> import Data.IORef
> import System.IO.Unsafe (unsafePerformIO)

> {-# NOINLINE doTrace #-}
> {-# NOINLINE trace #-}
> doTrace = unsafePerformIO (newIORef False)
> trace s x = unsafePerformIO (do b <- readIORef doTrace
>                                 when b (Trace.traceIO s)
>                                 return x)

We implement a pass suitable for combining with other portions of the front end.

> specializeProgram :: [Id] -> Pass () (Program KId, (Map Id (X.Scheme X.Type, Int), SolverEnv)) Specialized
> specializeProgram is (p, (ctors, senv)) = liftBase (specProgram [Inst i [] [] | i <- is] p ctors senv)

-------------------------------------------------------------------------------
-- Substitutions on Types:
-------------------------------------------------------------------------------

In the process of specializing the definition of value with a polymorphic type
to a particular monomorphic instance, we use a type substitution (TSubst) to
track the way in which individual type variables are instantiated.  The apply
function an be used to compute the instance of a given type under a particular
substitution; this will be useful, for example, when we need to calculate
appropriate type annotations for lambda bound variables that appear in the
specialized version of the code:

> apply                         :: TSubst -> Type -> Type
> apply s t = tyVarFree (s # t)
>     where tyVarFree (TyVar i)    = error ("Specializer TyVar: " ++ show i)
>           tyVarFree (TyApp t t') = TyApp (tyVarFree t) (tyVarFree t')
>           tyVarFree t            = t

The types that are produced by apply, as well as the types that are passed in
as part of the specified substitution are expected to be ground types, without
any type variables.  If this condition is not satisfied, then the original
program is ambiguous, and should have been rejected earlier in the pipeline
when there was still some way to access information about positions in source
file for use in error diagnostics.

As an example of the kind of ambiguity that we are describing here, consider
the following definition:

 f x = if null [] then x else x

Adding in the type and evidence parameters, this becomes:

 f{a,b}{} = \(x::a) -> if null{b}{} Nil{b}{} then x else x

Note that this function has *two* type parameters, but there is no way to
determine which type should be chosen for the second.  In this case we might
assume that the implementation of null Nil will always return True, regardless
of the type of empty list that we chose.  In general, however, we cannot be
sure of a well-defined semantics in such cases and the program should be
rejected.

-------------------------------------------------------------------------------
-- Evaluating Evidence:
-------------------------------------------------------------------------------

XMPEG programs use evidence expressions, represented by values of type Ev, to
document how implementations of overloaded operators can be obtained from the
set of class & instance declarations appearing in any given program.  Because
of the use of evidence variables and superclass selectors in Ev, a single type
class instance may be represented by many different evidence expressions.  For
the purposes of specialization, we introduce a mechanism for evaluating
evidence expressions to eliminate EvVar and EvSuper nodes and producing DApp
values as results.  Each DApp represents an application to type and dictionary
arguments.  Depending on the context in which it appears, the Id portion of a
DApp may be either the name of a user-level value or a dictionary constructor.

> data DApp = DApp Id [Type] [DApp]
>             deriving Eq

> instance Printable DApp
>     where ppr (DApp id ts ds) = ppr id <> braces (cat (punctuate ", " (map ppr ts)))

> instance HasTypeVariables DApp
>     where s # DApp id ts ds = DApp id (s # ts) (s # ds)

In general, an evidence expression of the form EvCons (Inst i ts es) will be
mapped to a value (DApp i ts' ds) which has essentially the same structure as
the original value (and, in particular, the same identifier i) except that the
the list of evidence expressions is replaced recursively by a list of DApps.
In addition to the type substitution that is used to translate ts into ts',
we will also need access to a substitution (of type DictSubst) that maps
evidence variables to DApp values (previously computed dictionaries), as well
as an evidence environment that provides implementations for each of the instance
declarations in the original program:

> type DictSubst = [(Id, DApp)]

Now we can describe the process of evaluating an evidence expression with a
given EvDecls, TSubst, and Dict Subst using the following function:

> matchEv :: [EvPat] -> [DApp] -> Maybe (TSubst, DictSubst)
> matchEv [] [] = return (empty, [])
> matchEv (EvWild : pats) (_ : evs) = matchEv pats evs
> matchEv (EvPat id ts ps : pats) (DApp id' ts' evs' : rest)
>     | id == id' = do s <- unify ts ts'
>                      (s', dcs) <- matchEv (s # pats) (s # rest)
>                      return (s' `compose` s, zip ps evs' ++ dcs)
>     | otherwise = Nothing

> evalEv :: EvDecls -> SolverEnv -> TSubst -> DictSubst -> Ev -> DApp
> evalEv env _ tys dcs (EvVar i)
>   = fromMaybe (error ("Unbound EvVar in specialization " ++ fromId i)) (lookup i dcs)
> evalEv env senv tys dcs (EvCons tapp)
>   = evalInst env senv tys dcs tapp
> evalEv env senv@(_, _, _, rqImpls, _) tys dcs (EvRequired n evs)
>   = case Map.lookup n rqImpls of
>       Nothing -> error ("No implementation of " ++ show n)
>       Just impls -> loop impls
>     where evs' = map (evalEv env senv tys dcs) evs
>           loop ((pats, body) : rest) =
>               case matchEv pats evs' of
>                 Just (tys', dcs') -> evalEv env senv (compose tys' tys) (dcs' ++ dcs) body
>                 Nothing -> loop rest
> evalEv env senv tys dcs (EvCases cs) = iter cs
>  where iter ((cond, ev) : rest) =
>            case cond `under` tys of
>              Nothing -> iter rest
>              Just _  -> evalEv env senv tys dcs ev
> evalEv env senv tys dcs (EvComputed args f)
>   = evalEv env senv tys dcs (f [tys # TyVar v | v <- args])
> evalEv env senv tys dcs (EvFrom pat e e')
>   = case matchEv [pat] [d] of
>       Just (tys', dcs') -> evalEv env senv (compose tys' tys) (dcs' ++ dcs) e'
>       Nothing           -> error (unlines [ "Specializer: expected evidence matching",
>                                             "     " ++ show (ppr pat),
>                                             "but found",
>                                             "     " ++ show (ppr d) ])
>     where d = evalEv env senv tys dcs e

A similar operation is proved for converting Inst values (which appear as
components of EvCons nodes) into DApp values:

> evalInst :: EvDecls -> SolverEnv -> TSubst -> DictSubst -> Inst -> DApp
> evalInst env senv tys dcs (Inst i ts es)
>   = DApp i (map (apply tys) ts) (map (evalEv env senv tys dcs) es)

-------------------------------------------------------------------------------
-- Specialization Monad
-------------------------------------------------------------------------------

The main specialization algorithm will be described using a monad that
simplifies the plumbing of EvDecls, TypSubst, and DictSubst values through the
computation, and allows for the generation of fresh names for the specialized
versions of functions.  We define the monad directly as follows, instead of
using monad transformers, because this gives more fine control over how each
of the components are used.

> newtype M a = M { runM :: EvDecls ->     -- defns of dictionary constructors
>                           SolverEnv ->   -- solver environment
>                           TSubst ->      -- mapping of types to type variables
>                           DictSubst ->   -- mapping of dictionaries to ev vars
>                           Types ->       -- records the set of types used
>                           Base (Types, a) }

The Types component records the set of (speicalized) types that are used.
Although the Type structure includes type variables, we assume that all types
in the list will be ground instances.  This implies that the type substitution
and the types components can't interact.

> type Types       = [Type]

Certain types are (potentially) required in every program because they can be
used in desugaring of if expressions and statements, &&, ||, etc., (or, for
Unit, because they will be used as the LambdaCase implementation of Lab l and
Nat n types).  The required types are:

> requiredTypes   :: Types
> requiredTypes    = [TyCon (Kinded "Unit" KStar), TyCon (Kinded "Bool" KStar)]

The monad structure for M is as follows:

> instance Functor M where
>  fmap f c = M (\env senv tys dcs rqts -> do (rqts1, x) <- runM c env senv tys dcs rqts
>                                             return (rqts1, f x))

> instance Applicative M
>     where pure = return
>           (<*>) = liftM2 ($)

> instance Monad M where
>  return x = M (\_ _ _ _ cs -> return (cs, x))
>  c >>= f  = M (\env senv tys dcs rqts -> do (rqts1, x) <- runM c env senv tys dcs rqts
>                                             runM (f x) env senv tys dcs rqts1)
>  -- TODO: does a stricter version of bind make any difference in practice?
>  -- c >>= f  = M (\env senv tys dcs rqts k -> case runM c env senv tys dcs rqts k of
>  --                                           (k1, rqts1, x) -> runM (f x) env senv tys dcs rqts1 k1)

> liftBaseToM :: Base a -> M a
> liftBaseToM b = M (\_ _ _ _ t -> b >>= \b' -> return (t, b'))

> instance MonadBase M where
>   fresh x      = liftBaseToM (fresh x)
>   getCounter   = liftBaseToM getCounter
>   putCounter x = liftBaseToM (putCounter x)

>   failWith d               = liftBaseToM (failWith d)
>   warn d                   = liftBaseToM (warn d)
>   failAt p c               = M (\e s t d ty -> failAt p (runM c e s t d ty))
>   transformFailures f c    = M (\e s t d ty -> transformFailures f (runM c e s t d ty))

The specName method handles the generation of names for specialized versions
of code.  If the entity that we are specializing does not have any type or
dictionary arguments, then there will only ever be one instance and we can
just reuse the original name.  Otherwise, we use the Int state component of
the monad to generate a fresh name (while still tracking the original name of
the item from which it was specialized).

> specName               :: DApp -> M Id
> specName (DApp i [] []) = return i
> specName (DApp i _ _)   = fresh i

We can run a computation with additional type and dictionary bindings by using
the following function.  We're essentially treating M as a reader monad for
the type and dictionary substitutions, except that we don't provide methods to
retrieve (or read) those components outside the set of monadic primitives
defined here.

> extend   :: TSubst -> DictSubst -> M a -> M a
> extend tys' dcs' c
>           = trace ("Binding:\n" ++ substStr tys') $
>             trace ("And:\n" ++ dictStr) $
>             M (\env senv tys dcs rqts -> runM c env senv (compose tys' tys) (dcs'++dcs) rqts)
>   where substStr s = unlines ["    " ++ fromId v ++ " +-> " ++ show (ppr t) | let S m = s, (Kinded v _, t) <- Map.assocs m]
>         dictStr = unlines ["    " ++ fromId v ++ " +-> " ++ show (ppr dapp) | (v, dapp) <- dcs']

We can find the appropriate instance of a type annotation using the current
(type) substitution by using the substitute operator:

> substitute  :: Type -> M Type
> substitute t = M (\_ _ tys _ rqts -> return (rqts, apply tys t))

Evidence expressions must be evaluated to eliminate superclass references and
to substitute for evidence variables.

> dictify  :: Inst -> M DApp
> dictify tapp = M (\env senv tys dcs rqts -> return (rqts, evalInst env senv tys dcs tapp))

When we encounter a method call, we need to find the dictionary that
contains the method implementation (by evaluating the first argument, ev);
find the appropriate dictionary constructor in the evidence environment;
select the appropriate method implementation (using the integer index, n);
and return the required specialization by supplying the appropriate lists
of type and dictionary parameters to the method implementation:

> method :: Ev -> Int -> [Type] -> [Ev] -> M DApp
> method ev n ts' es'
>   = M (\env senv tys dcs rqts ->
>           case evalEv env senv tys dcs ev of
>             DApp i ts ds ->
>               trace ("method: Requested: " ++ show (ppr (DApp i ts ds))) $
>               case Map.lookup i env of
>                 Nothing -> error ("Cannot find instance for method " ++ show n ++ " of " ++ fromId i)
>                 Just (_, Gen instTyParams instEvParams methods) ->
>                   let Gen methodTyParams methodEvParams m = methods!!n
>                       mts = map (apply tys) ts' ++ ts
>                       mes = ds ++ map (evalEv env senv tys dcs) es'
>                       tys' = compose (new (zip (methodTyParams ++ instTyParams) mts)) tys
>                       dcs' = (zip (instEvParams ++ methodEvParams) mes) ++ dcs
>                   in return (rqts, evalInst env senv tys' dcs' m))

To generate the specialized datatype declarations; we collect all types that appear in the
(unspecialized) program.  After specializing the program expressions, the list of required types
will be used to generate the specialized datatype declarations.

> requireType :: Type -> M ()
> requireType t
>   = M (\env _ _ _ rqts ->
>            if t `elem` rqts
>            then return (rqts, ())
>            else return (t : rqts, ()))

> withRequiredTypes :: ([Type] -> M t) -> M t
> withRequiredTypes c
>   = M (\env senv tys dcs rqts -> do (rqts1, x) <- runM (c rqts) env senv tys dcs rqts
>                                     return (rqts1, x))

Finally, we include an interface to the solver, used to discharge the
predicates introduced by qualified constructor patterns.  We assume that the
solver will succeed (that is, will find no contradictions and have no
remaining predicates).  From the solver result, we add the computed
improvement to the specializer type substitution, evaluate the returned
evidence values and add the result to the dictionary substitution.

> solve :: [(Id, Pred Type)] -> M t -> M (Maybe t)
> solve epreds c
>     = M (\env senv tys dcs rqts ->
>              let epreds' = [(id, tys # e) | (id, e) <- epreds]
>              in do k <- getCounter
>                    case entails senv ([], []) [] [] [] epreds' k of
>                      Left p -> return (rqts, Nothing)
>                      Right (evsubst, remaining, ks, impr, (_ :: [TypeBinding]), k') -- ASSUME: at this point, we shouldn't be getting conditional proofs
>                        | not (null remaining) -> return (rqts, Nothing)
>                        | otherwise ->
>                          let dcs' = [(id, evalEv env senv tys dcs ev) | (id, ev) <- evsubst]
>                          in do putCounter k'
>                                runM (Just `fmap` c) env senv (new impr `compose` tys) (dcs' ++ dcs) rqts)

-------------------------------------------------------------------------------
-- Specialization Contexts:
-------------------------------------------------------------------------------

Our implementation of specialization uses a collection of data structures that
we call "specialization contexts" to track mappings from DApp values to the
names of corresponding specialized versions.  We will actually use different
types of specialization context at different points in a program; we will use
a class to describe these types and the associated specialization lookup
functions that is needed in each case.  Ironically, this leads to a use of
type classes (and, indirectly, polymorphic recursion) that would prevent us
from compiling this code using specialization :-)

The key operation on specialization contexts is a function for looking up a
specialization for a particular DApp, returning a simple Expr for the
specialized entity in the final program (either an ELamVar or, for a
primitive, an ELetVar that includes a list of zero or more type parameters).
The operation also returns an updated context if the original did not already
specify an apropriate specialization.

> class SpecContext c where
>   specLookup :: DApp -> c -> M (Expr, Maybe c)

A specialization context is required to capture information about previously
specialized DApp values so that we do not create more than one specialization
of any given DApp.  If the original context already provides the requested
specialization, then the second component of the result returned by specLookup
will be Nothing, indicating that the context was not changed.  However, when a
given DApp is encountered for the first time, specLookup is expected to
generate a new Id (which is the primary reason for including a monad, M, in
the type), and to create a modified version of the context that captures the
new specialization.  In this case, the result that is produced by specLookup
will be a pair of the form (ELamVar i, Just c), where c is the new version of the
context and i is the name to use in place of the original DApp.

Specialization contexts are often built up in a stack like structure.  The
following function provides a general pattern for constructing an
implementation of specLookup in cases where a context of type c' is built on
top of a context of type c.  A call (specNest tapp c upd) takes care of
looking for a specialization in the lower context, c, returning an
identifier for the specialization of tapp as well as an updated version of
the context if necessary (the task of embedding a modified c context inside
the higher-level c' context is described by the upd function):

> specNest :: SpecContext c => DApp -> c -> (c -> c') -> M (Expr, Maybe c')
> specNest tapp c upd
>  = do (i, me) <- specLookup tapp c
>       case me of
>         Nothing -> return (i, Nothing)
>         Just c1 -> return (i, Just (upd c1))

In the implementation of specLookup for a context that is built on top of
lower-level contexts, we will typically start by looking for specializations
in the upper-levels before moving down in to lower levels.  The following
combinator captures a pattern that we will use in such cases.  The first
argument captures the result of trying to find a specialization in the
top-level context as a Maybe value; but if that results in Nothing, then we
can use the computation described by the second argument to search in lower
levels.

> specFrom        :: Maybe Id -> M (Expr, Maybe c) -> M (Expr, Maybe c)
> specFrom src alt = case src of
>                      Just i  -> trace ("Found: " ++ show (ppr i)) $
>                                 return (ELamVar i, Nothing)
>                      Nothing -> alt

An underlying assumption here is that, as we descend a stack of contexts, we
will eventually find (or create) an appropriate specialization.  The different
levels correspond to nested scopes in the source language, so failing to find
a specialization would correspond to an unbound variable, an error condition
that would have been detected and reported to the user in earlier stages of
the pipeline.

To illustrate these ideas, we will give a concrete definition of a context
that is intended to be used at the lowest level of a context stack.  Given the
assumption described in the previous paragraph about the lack of unbound
variables in the program, one might expect that such a context would not
contain any values.  However, we will use them instead to track the set of
primitives that are needed, none of which are defined at higher levels in the
context stack:

TODO: This used to hold a list of primitives, but it is now unused.

> data Primitives = Primitives

Requesting a new specialization from a Primitives level context either returns
the name for a previously requested specialization, or else picks a fresh name
and adds a new specialization.

> instance SpecContext Primitives where
>   specLookup dapp@(DApp n ts is) (Primitives)
>     = error $ "Unbound identifier: " ++ fromId n ++ " on " ++ (concat $ intersperse ", " $ map (show . ppr) ts)

Perhaps we will switch to a more efficient lookup operation/data structure
here in the future, but until then an association list like this will work
just fine.

-------------------------------------------------------------------------------
-- Walking the abstract syntax tree:
-------------------------------------------------------------------------------

The main specialization algorithm walks the abstract syntax tree looking for
places where specialization is required.  Candidates for specialization are
evaluated to produce corresponding DApp values that can then be used to look
for the name of the specialized version in the current context:

> specDApp :: SpecContext c => c -> DApp -> M (Expr, c)
> specDApp c dapp
>     = do (i, me) <- specLookup dapp c
>          case me of
>            Just c' -> return (i, c')
>            Nothing -> return (i, c)

Because we're implementing specialization as an XMPEG to XMPEG translation,
we can't completely eliminate the use of Inst values in an ELetVar, but we
can get close by using [] for the two list arguments.

There are two operations that we use to describe the process of traversing
the abstract syntax tree:

- specialize c e  computes a specialized version of e (expressions or matches)
  in the context c, also returning an updated version of the context.

> class Specialize e where
>   specialize :: SpecContext c => c -> e -> M (e, c)

- specOver c g m  computes specialized versions of g and m in the context c,
  but with the possibility that g could introduce new let bindings that are
  only in scope in m; uses of those local bindings in m will determine the
  set of specialized versions that are required in the specialization of g.
  This method is used for computing specializations involving patterns and
  guards.

> class SpecOver g where
>   specOver :: (SpecContext c, Specialize m) => c -> g -> m -> M (g, m, c)

The cases for specialization of an expression are given in the following
instance declaration:

> instance Specialize Expr where

>   specialize c (ELamVar i)
>     = return (ELamVar i, c)

>   specialize c (ELetVar tapp)
>     = dictify tapp >>= specDApp c

>   specialize c e@(EBits {})
>     = return (e, c)

>   specialize c (ECon tapp)
>     = dictify tapp >>= specDApp c

>   specialize c (ELam i t e)
>     = do (e', c') <- specialize c e
>          t'       <- substitute t
>          return (ELam i t' e', c')

>   specialize c (EMethod ev n ts es)
>     = method ev n ts es >>= specDApp c

>   specialize c (ELet ds e)
>     = do (e', c1)  <- specialize (enter ds c) e
>          (ds', c2) <- specDecls c1
>          return (ELet ds' e', c2)

>   specialize c (ELetTypes (Left cs) e)
>     = iter cs
>     where iter ((cond, impr):rest) =
>               M (\env senv tys dcs rqts ->
>                      case cond `under` tys of
>                        Nothing -> runM (iter rest) env senv tys dcs rqts
>                        Just _  -> runM (extend (new impr) [] (specialize c e)) env senv tys dcs rqts)

>   specialize c (ELetTypes (Right (args, results, f)) e)
>     = M (\env senv tys dcs rqts ->
>              runM (extend (new (zip results (f [tys # TyVar v | v <- args]))) [] (specialize c e))
>                   env senv tys dcs rqts)

>   specialize c (ESubst _ _ _)
>     = error "ESubst values should not appear in specialization"

>   specialize c (EMatch m)
>     = do (m', c') <- specialize c m
>          return (EMatch m', c')

>   specialize c (EApp f x)
>     = do (f', c1) <- specialize c f
>          (x', c2) <- specialize c1 x
>          return (EApp f' x', c2)

>   specialize c (EBind ta tb tm procEvid v e e')
>     = do (e1, c1) <- specialize c e
>          (e1',c2) <- specialize c1 e'
>          ta'      <- substitute ta
>          tm'      <- substitute tm
>          if isMachineMonad tm'
>            then -- Keep the EBind for the machine "monad":
>              do ta' <- substitute ta
>                 -- NOTE: tb' and procEvid are NOT updated here
>                 return (EBind ta' tb tm' procEvid v e1 e1', c2)
>            else -- Translate to a method call for other monads:
>                 let EvCons (Inst _ _ [monadEvid]) = procEvid
>                 in do (bind, c3) <- method monadEvid 1 [ta, tb] [] >>= specDApp c2
>                       return (EApp (EApp bind e1) (ELam v ta' e1'), c3)
>       where
>         isMachineMonad (TyCon (Kinded "M" _)) = True
>         isMachineMonad (TyCon (Kinded "I" _)) = True
>         isMachineMonad _                      = False

Specialization of Match constructs:

> instance Specialize Match where
>   specialize c MFail
>     = return (MFail, c)
>   specialize c (MCommit e)
>     = do (e', c') <- specialize c e
>          return (MCommit e', c')
>   specialize c (MElse m1 m2)
>     = do (m1', c1) <- specialize c m1
>          (m2', c2) <- specialize c1 m2
>          return (MElse m1' m2', c2)
>   specialize c (MGuarded (GLet ds) m)
>     = do (m', c1)  <- specialize (enter ds c) m
>          (ds', c2) <- specDecls c1
>          return (MGuarded (GLet ds') m', c2)
>   specialize c (MGuarded (GFrom p id) m)
>     = case p of
>         PWild ->
>           do (m', c1) <- specialize c m
>              return (MGuarded (GFrom PWild id) m', c1)
>         PVar i t ->
>           do (m', c1) <- specialize c m
>              t' <- substitute t
>              return (MGuarded (GFrom (PVar i t') id) m', c1)
>         PCon cinst is ->
>           do (m', c1) <- specialize c m
>              (r, c2) <- dictify cinst >>= specDApp c1
>              case r of
>                ECon (Inst cname ts' _) ->
>                    return (MGuarded (GFrom (PCon (Inst cname ts' []) is) id) m', c2)
>                _ -> error ("Oops! Found myself a " ++ show (ppr r) ++
>                            (case r of ELetVar _ -> " which is a (let-bound) variable!"
>                                       ELamVar _ -> " which is a (lambda-bound) variable!"
>                                       _ -> ""))

> {-
>           do r <- solve ebinds
>                         (do (m', c1) <- specialize c m
>                             (ECon (Inst _ ts' _), c2) <- dictify (Inst cname ts []) >>= specDApp c1
>                             return (MGuarded (GFrom (PCon cname ts' [] is) id) m', c2))
>              case r of
>                Nothing -> return (MFail, c)
>                Just (m', c2) -> return (m', c2)
> -}

>   specialize c (MGuarded (GLetTypes (Left cs)) m)
>     = iter cs
>     where iter ((cond, impr):rest) =
>               M (\env senv tys dcs rqts ->
>                      case cond `under` tys of
>                        Nothing -> runM (iter rest) env senv tys dcs rqts
>                        Just _  -> runM (extend (new impr) [] (specialize c m)) env senv tys dcs rqts)
>   specialize c (MGuarded (GLetTypes (Right (args, results, f))) m)
>     = M (\env senv tys dcs rqts ->
>              runM (extend (new (zip results (f [tys # TyVar v | v <- args]))) [] (specialize c m))
>                   env senv tys dcs rqts)



-------------------------------------------------------------------------------
-- Declarations
-------------------------------------------------------------------------------

We will use values of type Scope c as specialization contexts when we are in
the scope of a set of (mutually recursive) definitions:

> data Scope c         = Scope { defns   :: Map Id Defn,
>                                specd   :: [Specialization],
>                                reqd    :: [Specialization],
>                                numReqd :: Int,
>                                enc     :: c }
> type Defn            = (Scheme Type, Either (String, [Type]) (Gen Expr))
> type Specialization  = (DApp, Id, Defn)

Each such context captures:

- the original set of declarations, decls, converted into a Map from Id
  to Defn values;

- a list, specd, enumerating specialized versions of those definitions that
  have already been created;

- a list, reqd, containing specializations that have been requested but not
  yet created; and

- an integer recording the total number of specializations that have been
  requested (the sum of the lengths of specd and reqd); this is used as a
  heuristic for detecting programs that might require infinitely many
  distinct instances as a result of specialization.

- a context, enc, that will be used when a specialization is requested for
  an identifier that is defined in in an enclosing scope.

Each entry in the specd and reqd lists includes a Defn.  For reqd, each such
Defn is a cached copy of the definition for the function named in the tapp,
the target of future specialization.  For specd, these Defn values record the
specialized definitions that have been generated; they will eventually be
inserted in to the specialized program in a binding for the Id that is the
second component of the Specialization type.

When a set of decls is first encountered, we can use the enter function to
create a new specialization Scope context with appropriate values for each of
the fields:

> enter :: Decls -> c -> Scope c
> enter (Decls decls) c = Scope { defns, specd=[],
>                                 reqd=monoDefns, numReqd=length monoDefns,
>                                 enc=c }
>  where defns = foldr insertDefn Map.empty decls
>        insertDefn (X.Defn id scheme rhs) = Map.insert id (scheme, rhs)
>        monoDefns = [(DApp id [] [], id, (tys, body)) | d@(X.Defn id tys@(Forall [] [] _) body) <- decls]

Conversely, when there are no remaining specializations requests, we can use
the exit function to turn the list of specializations that have been computed
back into a list of declarations and recover the original specialization
context.

> exit  :: Scope c -> (Decls, c)
> exit c = (Decls ds, enc c)
>  where ds = [ X.Defn i scheme body | (_, i, (scheme, body)) <- specd c ]

Specialization in a Scope context begins by testing to see if the variable
that is mentioned in the given Inst is actually defined in this scope; if not,
then we simply defer to the enclosing context for a specialization.
Otherwise, we look for an existing specialization in the lists of already
specialized and requested items, and if neither of those is successful, then
we add a new request:

> instance SpecContext c => SpecContext (Scope c) where
>   specLookup dapp@(DApp id _ _) c
>    = case Map.lookup id (defns c) of
>        Nothing -> specNest dapp (enc c) (\e -> c{enc = e})
>        Just d  -> trace ("Requested: " ++ show (ppr dapp))
>                 $ specFrom (dapp `inSpecs` specd c)  -- Already specialized?
>                 $ specFrom (dapp `inSpecs` reqd c)   -- Already requested?
>                 $ do i <- specName dapp              -- Make a new request
>                      let n = numReqd c
>                      if n > maxExpand * Map.size (defns c)
>                        then error "specialization may produce infinite program; try again?"
>                        else trace ("Created: " ++ show (ppr i)) $
>                             return (ELamVar i, Just c{reqd = (dapp, i, d):reqd c,
>                                                       numReqd = n + 1})

> maxExpand = 5 :: Int    -- TODO: replace this with a more general mechanism
>                         -- that can be controlled from the command line

The code in this instance uses the following function to look for a simple
name associated with a particular specialization in either the specialized or
required lists of a Scope context:

> inSpecs          :: DApp -> [Specialization] -> Maybe Id
> dapp `inSpecs` ss = case [ i | (dapp', i, _) <- ss, dapp == dapp' ] of
>                       (i:_) -> Just i
>                       []    -> Nothing

The main specialization loop for a group of definitions uses the reqd list as
a queue in a loop that pulls off requests one at a time, constructs a
specialized version, adds that to the specialized list, and then repeats until
there are no further requests.  As part of this, we have to allow for the
possibility that new requests will be added to this level during the period
that we are constructing a specialized version of a definition.  To allow for
this, we define an additional form of specialization context to keep track of
a specialization that is being generated after it has been removed from reqd
but before it has been specialized and added to specd.

> data Constructing c = Constructing DApp Id c

Requesting a specialization from a Constructing context either returns the
name for the current Inst or else defers to the enclosing context:

> instance SpecContext c => SpecContext (Constructing c) where
>   specLookup dapp (Constructing dapp' i c)
>     | dapp == dapp' = return (ELamVar i, Nothing)
>     | otherwise     = specNest dapp c (Constructing dapp' i)


> specDecls :: SpecContext c => Scope c -> M (Decls, c)
> specDecls c
>   = case reqd c of
>       []         -> return (exit c)
>       (req:reqs) -> do (spec, c') <- respond req c{reqd = reqs}
>                        specDecls c'{specd = spec : specd c'}

> respond :: SpecContext c => Specialization -> Scope c -> M (Specialization, Scope c)
> respond (dapp, i, (Forall tvars evars t, body)) c
>     | length typeArgs < length tvars = error ("Unexpected polymorphism at specialization")
>     | otherwise =
>          trace ("Responding to " ++ show (ppr i) ++ "(" ++ show (ppr dapp) ++ ")") $
>          do (body', c') <- specBody body
>             t' <- substitute (inst typeArgs t)
>             requireType t'
>             return ((dapp, i, (Forall [] [] t', body')), c')
>     where DApp _ typeArgs dictArgs = dapp
>           specBody (Left (id, args)) = return (Left (id, args ++ typeArgs), c)
>           specBody (Right (Gen typeIds dictIds e)) = do
>               (e', Constructing _ _ c') <- extend tys dcs
>                   (specialize (Constructing dapp i c) e)
>               return (Right (Gen [] [] e'), c') where
>                   tys = new (zip typeIds typeArgs)
>                   dcs = zip dictIds dictArgs

We could also track the number of specialized functions that are generated
within a single level and trigger an error if this exceeds some specified
limit.  This would provide a mechanism for preventing nontermination; the
compiler might allow the limit to be adjusted by a compile time parameter so
that unusual programs that exceed the preset limit can still be compiled.  The
limit could be an absolute number (e.g., no more than X specialized functions
per let binding, or no more than X specialized versions of any single
function), or a multiplying factor (e.g., no more than X times as many
specialized functions as there are original definitions in a binding group).
It might also be appropriate to vary the limits that are used at different
levels.  At the top-level, for example, we might want to allow for more
specializations than within a nested scope.

Collecting required types is easy for normal values: their types are computed
when they are specialized.  Not necessarily so for constructors; this code
adds the step to compute the (otherwise unnecessary) type of constructors and
add those to the required types.  Additionally, the number of type arguments
to a constructor may be more than the number of arguments to its type, should
the constructor use existential types.  This code ensures that only those
arguments that appear in the type appear on the constructor.

> data Constructors c = Constructors (Map Id (Scheme Type, Int)) c

> instance SpecContext c => SpecContext (Constructors c)
>     where specLookup dapp@(DApp n ts is) c@(Constructors ctors enc)
>             = case Map.lookup n ctors of
>                 Nothing ->
>                   specNest dapp enc (\enc -> Constructors ctors enc)
>                 Just (Forall _ _ t, i) ->
>                   do requireType =<< substitute (inst ts t)
>                      return (ECon (Inst n (drop i ts) []), Just c)

-------------------------------------------------------------------------------
-- Specialization of a Complete Program:
-------------------------------------------------------------------------------

Specialization of a complete XMPEG program is described by the following
function, which takes a Inst value specifying the program entry point (e.g.,
"main").  We also scan all of the top-level declarations for references to
top-level values (such as initializers or defauls) to ensure that they are
carried over into the specialized program.  Note that the evidence portion of
a specialized program will be set to Map.empty; the instance constructor
functions are not needed and may cease to be valid after specialization (if,
for example, they contain references to variables that are not a part of the
specialized code).

> specProgram :: [Inst] -> Program KId -> Map Id (Scheme Type, Int) -> SolverEnv -> Base Specialized
> specProgram tapps prog ctors senv = do
>   (rqts, (entries, topDecls'', decls', Constructors _ (Primitives))) <-
>     runM work (evidence prog) senv empty [] requiredTypes
>   return (Specialized topDecls'' entries decls')
>     where
>       doEntries c []     = return ([], c)
>       doEntries c (e:es) = do (e', c1) <- specialize c (ELetVar e)
>                               (es', c2) <- doEntries c1 es
>                               return (e':es', c2)
>       work  = do (entries, c)    <- doEntries scope tapps
>                  (topDecls', c1) <- specialize c (topDecls prog)
>                  (decls', c2)    <- specDecls c1
>                  topDecls''      <- withRequiredTypes (selectTopDecls topDecls')
>                  return (entries, topDecls'', decls', c2)
>       scope = enter (filterDecls notConstructor (decls prog)) (Constructors ctors (Primitives))
>       filterDecls p (X.Decls defns) = X.Decls (filter p defns)
>       notConstructor (X.Defn name _ (Left _)) = name `notElem` (Map.keys ctors)
>       notConstructor _                        = True




> instance Specialize e => Specialize [e] where
>   specialize c []     = return ([], c)
>   specialize c (e:es) = do (e', c1)  <- specialize c e
>                            (es', c2) <- specialize c1 es
>                            return (e':es', c2)

> instance Specialize (TopDecl KId) where
>   specialize c d@(Datatype id params ctors) = return (d, c)
>   specialize c d@(Bitdatatype id w ctors)   = return (d, c)
>   specialize c d@(Struct id w fields)       = return (d, c)
>   specialize c d@(Area v ids ty w a)
>    = do (ids', c') <- specIds c ids
>         return (Area v ids' ty w a, c')
>      where specIds c [] = return ([], c)
>            specIds c ((id, tapp):ids)
>              = do (e,c1)     <- dictify tapp >>= specDApp c
>                   (ids', c2) <- specIds c1 ids
>                   return ((id, toInst e):ids', c2)
>            toInst (ELamVar i)    = Inst i [] []
>            toInst (ELetVar tapp) = tapp

Find a list of the area initializers mentioned in top-level area declarations,
each of which is described by a Inst.  (Although these initializers must have
monomorphic types, it is possible for their definitions to use types that include
quantified variables and predicates as a result of using functional notation and
type synonyms.)

> areaIds                   :: TopDecl typaram -> [Inst]
> areaIds (Area _ areas _ _ _) = [ ini | (_, ini) <- areas ]
> areaIds _                    = []

-------------------------------------------------------------------------------
-- Specialization of Datatype Declarations:
-------------------------------------------------------------------------------

Specialization collects the set of all constructor instances that appear within
a given program.  Our task now is to turn that into a list of specialized data
type definitions.

This is slightly complicated as we may require specialized versions of type that
are not constructed anywhere in the program.  Consider the following example:

  data Cake      = Birthday | Wedding
  data MaybeCake = HaveSome Cake | TheCakeIsALie

  main = return TheCakeIsALie

In this case, despite neither 'Birthday' nor 'Wedding' appearing in the program,
we need to include the Cake type in the specialized output or the MaybeCake type
will refer to an undefined type.  Similarly, consider the above declarations and
the function definition:

  f :: MaybeCake -> Int
  f _ = 0

In this case, neither the constructors for MaybeCake nor Cake appear in the
program, yet both must be included in the specialized program.

Further complications are introduced by qualified constructors: some of the
qualifiers for individual branches of the qualified constructor may be
contradicted for any particular specialized version.  When specializing a
declaration with qualified constructors, we attempt to discharge the
qualifiers for each branch at the specialzed type; if it is impossible to do
so, we exclude that constructor from the qualified version.

TODO: This makes it possible to generate an empty datatype declaration.  Will
this cause problems later in the pipeline?

> selectTopDecls :: [TopDecl KId] -> [Type] -> M [TopDecl Type]
> selectTopDecls topDecls rqtys
>   = do (areas', areaRqts) <- unzip `fmap` mapM specArea topDecls
>        topDecls' <- iter [] (concat areaRqts ++ rqtys)
>        return (catMaybes areas' ++ topDecls')
>   where iter built [] = return (map snd built)
>         iter built (rq : rqs)
>             | kindOf rq /= KStar = iter built rqs
>             | rq `elem` map fst built = iter built rqs
>             | otherwise = case topDeclFor rq topDecls of
>                             Nothing -> iter built (concatMap requestedBy (snd (flattenType rq)) ++ rqs)
>                                        -- avoid attempting to build primitive types, but include arguments to primitive types
>                             Just d  -> do (d', newRqs) <- specTopDecl d rq
>                                           let builtTys     = map fst built
>                                               newRqs'      = filter (`notElem` builtTys) newRqs
>                                           iter ((rq, d') : built) (newRqs' ++ rqs)

>         specArea (Area v ids ty size align)
>           = return (Just (Area v ids ty size align), requestedBy ty)
>         specArea _
>           = return (Nothing, [])

> topDeclFor :: Type -> [TopDecl KId] -> Maybe (TopDecl KId)
> topDeclFor t topDecls
>     = case flattenType t of
>         (TyCon (Kinded id _), _) -> lookFor id topDecls
>         _ -> Nothing

>     where lookFor id [] = Nothing
>           lookFor id (d@(Datatype id' _ _) : _)
>             | id == id' = Just d
>           lookFor id (d@(Bitdatatype id' _ _) : _)
>             | id == id' = Just d
>           lookFor id (d@(Struct id' _ _) : _)
>             | id == id' = Just d
>           lookFor id (_ : ds) = lookFor id ds

> specTopDecl :: TopDecl KId -> Type -> M (TopDecl Type, [Type])
> specTopDecl (Datatype name params ctors) ty
>   = do (ctors', requested) <- unzip `fmap` mapM spec ctors
>        return (Datatype name ts (catMaybes ctors'), concat requested)
>     where (_, ts) = flattenType ty
>           s       = new (zip params ts)

>           spec (name, kids, ps, ts)
>             = do enames <- replicateM (length ps) (fresh "e")
>                  ts'' <- solve (zip enames ps')
>                                (mapM substitute ts')
>                  case ts'' of
>                    Nothing   -> return (Nothing, [])
>                    Just ts'' -> return (Just (name, [], [], ts''), concatMap requestedBy ts'')
>               where newTys = [TyVar v | v <- kids]
>                     ps'    = [Pred className (map ((s #) . inst newTys) ts) f | Pred className ts f <- ps]
>                     ts'    = map ((s #) . inst newTys) ts

> specTopDecl (Bitdatatype name size conSpecs) _ = return (Bitdatatype name size conSpecs, requested)
>     where requested = concatMap requestedBy [ty | (_, fields, _) <- conSpecs, LabeledField _ ty _ _ <- fields]
> specTopDecl (Struct name size fields) _ = return (Struct name size fields, requested)
>     where requested = concatMap requestedBy [ty | StructField _ ty _ _ <- fields]
> specTopDecl d t = error ("Unexpected call to specTopDecl for declaration\n    " ++ show (ppr d) ++ "\nat type " ++ show (ppr t))

> requestedBy t = t : snd (flattenType t)
