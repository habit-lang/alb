{-# LANGUAGE FunctionalDependencies, FlexibleContexts, FlexibleInstances,
          GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeSynonymInstances,
          UndecidableInstances, OverloadedStrings #-}
module Analyzer.Desugaring (desugarProgram, DesugaringState) where

-- This module eliminates much of the sugar of the surface syntax, generating the implicitly typed
-- intermediate language used for type checking.  In the process, we perform some verification, such
-- as checking that variable and constructor names are in scope, equations are valid definitions,
-- etc.

import Control.Monad.Reader
import Control.Monad.State
import Data.Char (isUpper, isAlpha)
import Data.Either (partitionEithers)
import Data.Foldable (foldrM)
import Data.Graph (SCC(..), stronglyConnComp)
import qualified Data.IntSet as Set
import Data.List
import qualified Data.Map as Map
import Data.Maybe (catMaybes)

import Common
import Printer.Common ((<+>), text)
import Printer.Surface
import Printer.IMPEG hiding (paramName)
import qualified Syntax.Surface as S
import Syntax.IMPEG hiding (replacement)
import qualified Syntax.IMPEG.KSubst as K
import Syntax.IMPEG.TSubst

-- DONE: factor out tuples
-- DONE: factor out isBound
-- DONE: duplicate name checking (leaving it in for now)

-- TODO: add checking for Ctors being in scope
-- TODO: toScheme as post desugar pass??
-- TODO: nullary??
-- TODO: commuteLambdas as a post-desugar optimization
-- TODO: why can't we have variables in instances? (warn on non-function instance method?)
-- TODO: gen??
-- TODO: rejectDuplicates

----------------------------------------------------------------------------------------------------
-- Translation monad
----------------------------------------------------------------------------------------------------

type ScopeEnv = Map.Map Id (Located Id)
type CtorEnv  = ([(Id, Bool)], [Id])    -- (bitdata ctors (id, nullary), struct ctors)

-- The translation monad, M.  M tracks the field map, a set of fixities (used in rewriting infix
-- expressions to their prefix equivalents), the scope environment, an integer for fresh name
-- generation, and indicates errors a pair of an (optional) source location and error message.

newtype M t = M { runM :: ReaderT CtorEnv Base t }
    deriving (Functor, Applicative, Monad, MonadBase, MonadReader CtorEnv)

bindCtors :: CtorEnv -> M t -> M t
bindCtors (bitCtors, structCtors) = local (\(bitCtors', structCtors') ->
                                               (bitCtors ++ bitCtors', structCtors ++ structCtors'))

----------------------------------------------------------------------------------------------------
-- Desugaring
----------------------------------------------------------------------------------------------------

-- The 'desugar' function is overloaded to perform desugaring on most syntax tree nodes.

class Sugared t u | t -> u
    where desugar :: t -> M u

-- We can lift desugaring through standard constructors.

instance Sugared t u => Sugared (Located t) (Located u)
    where desugar (At p t) = failAt p (At p `fmap` desugar t)

instance Sugared t u => Sugared (Maybe t) (Maybe u)
    where desugar Nothing = return Nothing
          desugar (Just t) = Just `fmap` desugar t

instance (Sugared t t', Sugared u u') => Sugared (t, u) (t', u')
    where desugar (x, y) = liftM2 (,) (desugar x) (desugar y)

----------------------------------------------------------------------------------------------------
-- Types and Predicates

tupleName :: Int -> Id
tupleName n = fromString ("$Tuple" ++ show n)

instance Sugared S.Type (Type Id)
    where desugar (S.TyCon id) = return (TyCon id)
          desugar (S.TyVar id) = return (TyVar id)
          desugar S.TyWild = failWithS "Unexpected type wildcard"
          desugar (S.TyApp t t') = liftM2 TyApp (desugar t) (desugar t')
          desugar (S.TyNat l)  = return (TyNat l)
          desugar e@(S.TyTuple _) = failWith $ text "Internal error: tuple type at desugaring: " <+> ppr e
          desugar e@(S.TyTupleCon _) = failWith $ text "Internal error: tuple type constructor at desugaring: " <+> ppr e
          desugar (S.TyKinded t k) =
              do t' <- desugar t
                 return (TyKinded t' k)
          desugar (S.TyLabel id) = return (TyLabel id)
          desugar (S.TySelect t (At p l)) =
              desugar (dislocate (app [introduced (S.TyCon "Select"), t, At p (S.TyLabel l)]))
              where app = foldl1 (\t t' -> at t (S.TyApp t t'))
          desugar e@(S.TyInfix head tail) = failWith $ text "Internal error: infix type at desugaring: " <+> ppr e

instance Sugared S.Pred (PredType PredFN Id)
    where desugar (S.Pred t mt f) =
              do t' <- desugar t
                 mt' <- desugar mt
                 case flattenType t' of
                   (At _ (TyCon id@(Ident (c:_) _ _)), ts) | isUpper c || not (isAlpha c) ->
                        return (PredFN id ts mt' f)
                   _ -> failWithS "Predicate must consist of a tyconsym applied to a list of types"

instance Sugared (S.Qual S.Type) (Qual (PredType PredFN Id) (Type Id))
    where desugar (ps S.:=> t) = liftM2 (:=>) (mapM desugar ps) (desugar t)

instance Sugared (S.Qual S.Pred) (Qual (PredType PredFN Id) (PredType PredFN Id))
    where desugar (ps S.:=> t) = liftM2 (:=>) (mapM desugar ps) (desugar t)

-- toScheme ids qty generates a new type scheme that quantifies over all the variables in qty that
-- are not in ids.
toScheme ::  [Id] -> Qual (PredType PredFN Id) (Type Id) -> Scheme PredFN Id
toScheme retained qty = Forall vs (gen 0 vs qty)
    where vs = nub (tvs qty) \\ retained

toKScheme :: [Id] -> [Id] -> Qual (PredType PredFN Id) (Type Id) -> KScheme (Scheme PredFN Id)
toKScheme retained retainedTyVars qty = ForallK kvs (toScheme retainedTyVars qty)
    where kvs = filter (`notElem` retained) (K.vars qty)

----------------------------------------------------------------------------------------------------
-- Expressions

-- Shortcuts for constructing expressions: in particular, this handles inserting valid locations for
-- applications.
(@@) :: Located S.Expr -> Located S.Expr -> Located S.Expr
e @@ e' = at e (S.EApp e e')
infixl 9 @@

app :: Id -> [Located S.Expr] -> S.Expr
app op args = dislocate (foldl (@@) (introduced (S.EVar op)) args)

gfrom :: Pattern PredFN Id -> Expr PredFN Id -> Guard PredFN Id
gfrom p e = GFrom (introduced p) (introduced e)

sfield :: Location -> Id -> Located S.Expr
sfield l f = At l (S.ETyped (At l (S.ECon "Proxy"))
                            ([] S.:=> At l (S.TyApp (At l (S.TyCon "Proxy")) (At l (S.TyLabel f)))))

instance Sugared S.Expr (Expr PredFN Id)
    where desugar (S.ELet decls body) =
              do decls' <- desugar decls
                 body' <- desugar body
                 return (ELet decls' body')

          -- if<- and case<- are handled first by binding the scrutinee to a new value, and then
          -- rewriting a normal if/case expression.
          desugar (S.EIf (S.ScFrom mid cond) cons alt) =
              do name <- maybe (fresh "condition") return mid
                 liftM2 (EBind name)
                        (desugar cond)
                        (introduced `fmap`
                          desugar (S.EIf (S.ScExpr (introduced (S.EVar name))) cons alt))
          desugar (S.ECase (S.ScFrom mid scrutinee) alts) =
              do name <- maybe (fresh "scrutinee") return mid
                 liftM2 (EBind name)
                        (desugar scrutinee)
                        (introduced `fmap`
                          desugar (S.ECase (S.ScExpr (introduced (S.EVar name))) alts))

          -- if cond cons alt is rewritten to the match { True <- cond => ^cons | ^alt }; note that
          -- we're (now) avoiding the unnecessary check for False in the alternative branch.
          desugar (S.EIf (S.ScExpr cond) cons alt) =
              do cond' <- desugar cond
                 cons' <- desugar cons
                 alt' <- desugar alt
                 name <- fresh "condition"
                 return (EMatch (MGuarded (GFrom (introduced (PVar name)) cond')
                                 ((MGuarded (gfrom (PCon "True" []) (EVar name)) (MCommit cons')) `MElse`
                                  (MCommit alt'))))

          -- We begin a case by binding the scrutinee to a new value; this avoids recomputing it for
          -- each guard in the match.
          desugar (S.ECase (S.ScExpr scrutinee) alts) =
              do name <- fresh "scrutinee"
                 scrutinee' <- desugar scrutinee
                 alts' <- foldl1 MElse `fmap` mapM (desugarAlt name) alts
                 return (EMatch (MGuarded (GFrom (introduced (PVar name)) scrutinee') alts'))
              where -- Alternative may bind new names.  We begin by constructing replacements for
                    -- any bound names that would shadow existing definitions; after this,
                    -- desugaring the alternative is straightforward.
                    desugarAlt name (p S.:-> rhs) =
                        do p'@(At l _) <- desugar p
                           rhs' <- desugar rhs
                           return (MGuarded (GFrom p' (At l (EVar name))) rhs')

          -- The majority of the work for ELam is actually handled by desugarParameterList (defined
          -- far below) which handles the details of desugaring patterns and introducing new
          -- parameter names when necessary.
          desugar (S.ELam patterns body) =
              do (args', body') <- desugarParameterList patterns (MCommit `fmap` desugar body)
                 return (dislocate (foldr elam (introduced (EMatch body')) args'))
              where elam v body = introduced (ELam v body)

          desugar e@(S.EVar id) = return (EVar id)
          desugar (S.ECon id) =
              do (bitCtors, structCtors) <- ask
                 case lookup id bitCtors of
                   Just nullary   | nullary   -> return (EBitCon id [])
                                  | otherwise -> return (ECon id)
                   _  | id `elem` structCtors -> return (EStructInit id [])
                      | otherwise             -> return (ECon id)

          desugar (S.ELit (S.BitVector value size)) =
              return (EBits value size)
          desugar (S.ELit (S.Numeric value)) =
              dislocate `fmap` desugar (introduced (S.EVar "fromLiteral") @@ introduced proxy)
              where proxyType = [] S.:=> introduced (S.TyApp (introduced (S.TyCon "Proxy")) (introduced (S.TyNat value)))
                    proxy     = S.ETyped (introduced (S.ECon "Proxy")) proxyType


          desugar e@(S.ETuple _) = failWith $ text "Internal error: tuple expression at desugaring: " <+> ppr e
          desugar e@(S.ETupleCon _) = failWith $ text "Internal error: tuple constructor expression at desugaring: " <+> ppr e

          desugar (S.EApp (At _ (S.EApp (At _ (S.EVar "||")) lhs)) rhs) =
              do name <- fresh "scrutinee"
                 lhs' <- desugar lhs
                 rhs' <- desugar rhs
                 return (EMatch (MGuarded (GFrom (introduced (PVar name)) lhs')
                                          ((MGuarded (gfrom (PCon "False" []) (EVar name)) (MCommit rhs'))
                                           `MElse` MCommit (at lhs (EBitCon "True" [])))))

          desugar (S.EApp (At _ (S.EApp (At _ (S.EVar "&&")) lhs)) rhs) =
              do name <- fresh "scrutinee"
                 lhs' <- desugar lhs
                 rhs' <- desugar rhs
                 return (EMatch (MGuarded (GFrom (introduced (PVar name)) lhs')
                                          ((MGuarded (gfrom (PCon "True" []) (EVar name)) (MCommit rhs'))
                                           `MElse` MCommit (at lhs (EBitCon "False" [])))))

          desugar (S.EApp e e') = liftM2 EApp (desugar e) (desugar e')

          desugar (S.EBind Nothing e rest) =
              do v <- fresh "x"
                 liftM2 (EBind v) (desugar e) (desugar rest)
          desugar (S.EBind (Just v) e rest) =
              do e' <- desugar e
                 rest' <- desugar rest
                 return (EBind v e' rest')

          -- e.l is rewritten to the application select e l; similarly, e[l = e'] is rewritten to
          -- update e l e'
          desugar (S.ESelect e (At p l)) =
              desugar (app "select" [e, sfield p l])

          desugar (S.EUpdate (At _ (S.ECon id)) []) =
              do (bitCtors, structCtors) <- ask
                 case lookup id bitCtors of
                   Just _                     -> return (EBitCon id [])
                   _  | id `elem` structCtors -> return (EStructInit id [])
                      | otherwise             -> failWithS ("Constructor "++ fromId id ++" does not support empty update")
          desugar (S.EUpdate (At _ (S.ECon id)) fs) =
              do fs' <- mapM desugarBinding fs
                 return (EBitCon id fs')
              where desugarBinding (At _ name, e) =
                        do e' <- desugar e
                           return (name, e')
          desugar (S.EUpdate e fs) =
              desugar (dislocate (foldl update e fs))
              where update e (At p id, val) =
                        introduced (S.EVar "update") @@ e @@ sfield p id @@ val

          -- Sections are uniformly rewritten to lambdas
          desugar (S.ELeftSection lhs (At p opname)) =
              do rhs <- fresh "rhs"
                 desugar (S.ELam [introduced (S.PVar rhs)] (At p (S.EVar opname) @@ lhs @@ introduced (S.EVar rhs)))
          desugar (S.ERightSection (At p opname) rhs) =
              do lhs <- fresh "lhs"
                 desugar (S.ELam [introduced (S.PVar lhs)] (At p (S.EVar opname) @@ introduced (S.EVar lhs) @@ rhs))

          desugar (S.EStructInit (At _ name) fields) = liftM (EStructInit name) (mapSndM desugar fields)

          -- An expression:
          --    e :: sigma
          -- is equivalent to
          --    let x :: sigma; x = e in x
          desugar (S.ETyped e ty) =
              do v <- fresh "x"
                 e' <- desugar e
                 tys <- toKScheme [] [] `fmap` desugar ty
                 return (ELet (Decls [Explicit (v, [], MCommit e') tys]) (introduced (EVar v)))

          desugar e@(S.EInfix head tail) = failWith $ text "Internal error: infix expression at desugaring:" <+> ppr e

-- declsToMatch abstracts the construction of let guards from local declaration blocks.  As the
-- construction of the internal match needs to take the symbols and replacements from the outer
-- declaration block into account, we take a computation to construct the inner match instead of the
-- match itself.
declsToMatch :: Maybe S.Decls -> M (Match PredFN Id) -> M (Match PredFN Id)
declsToMatch Nothing c = c
declsToMatch (Just ds) c =
    do ds' <- desugar ds
       m <- c
       return (MGuarded (GLet ds') m)

instance Sugared S.Rhs (Match PredFN Id)
    where desugar (S.Unguarded body ds) =
              declsToMatch ds (MCommit `fmap` desugar body)
          desugar (S.Guarded ps ds) =
              declsToMatch ds $
              do ps' <- mapM desugar ps
                 vs <- replicateM (length ps') (fresh "condition")
                 return (foldl1 MElse [ MGuarded (GFrom (introduced (PVar v)) condition)
                                         (MGuarded (gfrom (PCon "True" []) (EVar v))
                                          (MCommit body))
                                      | (v, (condition, body)) <- zip vs ps' ])

----------------------------------------------------------------------------------------------------
-- Patterns and parameters

-- Note that we don't check pattern variables against the variables in scope or anything; computing
-- replacements is the responsibility of the code that handles the scoping node (such as a case
-- statement, above, or an equation in a declaration block, below).

instance Sugared S.Pattern (Pattern PredFN Id)
    where desugar S.PWild     = return PWild
          desugar (S.PVar id) = return (PVar id)
          desugar (S.PTyped p ty) = liftM2 PTyped (desugar p) (toScheme [] `fmap` desugar ty)

          -- A literal pattern l is interpreted as a guarded pattern (var | let test = var == l,
          -- True <- test) for some new variables var and test.  (The introduction of test is
          -- necessary to preserve the invariant, required in later stages, that the expression on
          -- the right of a PGuarded is a variable.
          desugar (S.PLit l) =
              do var  <- fresh "x"
                 test <- fresh "test"
                 l'   <- desugar (S.ELit l)
                 let testExpr = introduced (EApp (introduced (EApp (introduced (EVar "=="))
                                                                   (introduced (EVar var))))
                                                 (introduced l'))
                 return ((PVar var `PGuarded` GLet (Decls [Implicit [(test, [], MCommit testExpr)]]))
                                   `PGuarded` gfrom (PCon "True" []) (EVar test))

          -- x@p is equivalent to the guarded pattern (x | p <- x)
          desugar (S.PAs id p) =
              do p' <- desugar p
                 return (PGuarded (PVar id) (GFrom p' (introduced (EVar id))))

          -- The surface syntax supports arbitrary application in patterns; this is so that we don't
          -- have to sort out function definitions vs constructor applications during parsing.
          -- IMPEG, however, lacks PApp and associates the arguments of a constructor pattern with
          -- the pattern itself.  When desugaring a PApp, we desugar each side and then try
          -- flattening the LHS: if the far left argument is a PCon, we add the rest of the patterns
          -- to its arguments; otherwise, we fail.  An additional complication is that IMPEG insists
          -- that the arguments to a PCon all be variables; fixing this is separated into
          -- buildGuardedPattern.
          desugar (S.PCon id) = return (PCon id [])
--              do (bitCtors, _) <- ask
--                 case lookup id bitCtors of
--                   Just nullary | nullary -> do v <- fresh "v"
--                                                return (PCon id [v])
--                   _                      -> return (PCon id [])
--
          desugar e@(S.PTuple _) = failWith $ text "Internal error: tuple pattern at desugaring: " <+> ppr e
          desugar e@(S.PTupleCon _) = failWith $ text "Internal error: tuple constructor pattern at desugaring: " <+> ppr e
          desugar p@(S.PApp {}) =
              case op of
                At _ (S.PCon name) -> buildGuardedPattern name =<< mapM desugar ps
                _ -> failWith $ text "Pattern must be the application of a constructor to a list of arguments: " <+> ppr p
              where (op, ps) = S.flattenPattern (introduced p)

          desugar (S.PLabeled ctor fieldPatterns) =
              do rejectDuplicates [ At loc f | At loc (S.FieldPattern f p) <- fieldPatterns ]
                 n <- fresh "n"
                 foldM (addFieldGuards n) (PCon ctor [n]) fieldPatterns
              where
                -- For each field pattern field = p, add guards (...| let v = src.field, p <- v)
                addFieldGuards n pat (At loc (S.FieldPattern field p))
                  = do v  <- fresh "f"  -- variable to represent this field name
                       p' <- desugar p
                       At _ body <- desugar (At loc (S.EVar "select") @@ At loc (S.EVar n) @@ sfield loc field)
                       return ((pat `PGuarded` GLet (Decls [Implicit [(v,[],MCommit (At loc body))]]))
                                    `PGuarded` GFrom p' (introduced (EVar v)))

          desugar e@(S.PInfix head tail) = failWith $ text "Internal error: infix expressions/types at desugaring: " <+> ppr e

-- buildGuardedPattern takes a nested pattern and constructs an unnested pattern.  The basic notion
-- is that given a pattern of the form C (D p), this is equivalent to the guarded pattern (C x | D p
-- <- x) for a fresh variable x.  buildGuardedPattern performs this transformation recursively until
-- there are no nested patterns remaining.  One transformation that is not performed yet is to
-- remove guards of the form _ <- e; this ought to be relatively simple to add.
buildGuardedPattern :: Id -> [Located (Pattern PredFN Id)] -> M (Pattern PredFN Id)
buildGuardedPattern name ps =
    do (vs, guards) <- unzip `fmap` (mapM toGuard ps)
       return (foldl PGuarded (PCon name vs) (catMaybes (zipWith (\v g -> fmap (flip GFrom (introduced (EVar v))) g) vs guards)))
    where toGuard (At _ (PVar v)) = return (v, Nothing)
          toGuard p               = do v <- fresh "p"
                                       return (v, Just p)

-- That's fine and all, but when building functions (either in ELam above or when handling equations
-- below) we need to split a list of patterns into a list of parameters and a match, so we define a
-- helper function that desugars a list of patterns and an expression into (a) a list of variables
-- and (b) a match.  The final assembly of these parts is different in the two cases above.
desugarParameterList :: [Located S.Pattern] -> M (Match PredFN Id) -> M ([Id], Match PredFN Id)
desugarParameterList ps c =
    do body <- c
       foldM desugarPattern ([], body) (reverse ps)
    where desugarPattern (args, body) p =
              do p' <- desugar p
                 case p' of
                   At loc (PVar s) -> return (s : args, body)
                   _               -> do var <- fresh "x"
                                         return (var : args, MGuarded (GFrom p' (introduced (EVar var))) body)

----------------------------------------------------------------------------------------------------
-- Local declaration blocks

-- The majority of the confusion in this module is in handling declaration blocks.  There are
-- several issues that arise at this point:
--
--  * The first confusion is figuring out what is actually being defined; all we get from the parser
--    are patterns, which can either correspond to value bindings (a top level application of a
--    constructor to a list of patterns) or function bindings (a top level application of variable
--    to a list of patterns).  The possible presence of infix expressions further complicates this:
--    we'd like to use the correct fixities when resolving the LHS's, but as we don't yet know which
--    values are being defined, we can't compute replacements yet.
--
--  * Once we've disentangled the LHS's, we can determine what the block defines, whether any of
--    those identifiers shadow higher-level bindings, and compute replacements if they do.  With the
--    new bindings and replacements in hand, we can desugar the RHS's of the equations.
--
--  * Next, we need to combine multiple equations defining functions into single definitions,
--    sticking the different set of patterns together into matches.  We don't do this with much
--    intelligence at this point.  For example, given the equations:
--
--      f (Just x) (Just y) = ..
--      f (Just x) _        = ..
--      f _ _               = ..,
--
--    we'll generate two identical pattern matches against the first parameter.
--
--  * Finally, we need to combine the definitions into group for typechecking.  The notion here is
--    that we need to typecheck mutually recursive functions together to be able to compute types at
--    all; however, if we include extra definitions we may compute types that are too restrictive.
--    A further observation is that we can always check explicitly typed bindings separately: in the
--    remainder of the program, we can assume that the signature is valid.  To compute theses
--    groups, we perform an SCC over a graph where declarations are vertices and edges are
--    references without type signatures.

instance Sugared S.Decls (Decls PredFN Id)
    where desugar decls =
              do -- First, split the equations into their left- and right-hand sides.
                 let (lhss, rhss) = unzip [(lhs, rhs) | lhs S.:= rhs <- S.equations decls]
                 -- Split bindings into value and function definitions (and indicate errors for
                 -- others).
                 lhss' <- mapM splitPattern lhss
                 -- Figure out what we're actually defining
                 -- Now we can finally desugar the right hand sides.
                 equations <- mapM desugarEquation (zip lhss' rhss)
                 -- And merge sequential equations defining cases of the same function.  This will
                 -- fail if equations defining the same symbol are interlaced with equations
                 -- defining different symbols.
                 (valDefs, fcnDefs) <- partitionEithers `fmap` mergeEquations equations
                 let valNames = concatMap (bound . fst) valDefs
                     fcnNames = [id | (id, _, _) <- fcnDefs]
                     names = valNames ++ fcnNames

                 signatures <- mapM desugar (S.signatures decls)
                 let explicitlyTyped = [name | Signature name _ <- signatures]

                 when (hasDuplicates names) $
                      failWithS "Duplicate symbol definition"
                 when (any (`notElem` names) explicitlyTyped) $
                      failWithS ("Signatures without definition: " ++ intercalate "," (map fromId (filter (`notElem` names) explicitlyTyped)))
                 -- Finally, we perform the SCC ...
                 let simpleGroups = [(Left (p, e), i, bound p, freeVariables e \\ explicitlyTyped) | (i, (p, e)) <- zip [0,2..] valDefs] ++
                                    [(Right (name, args, body), i, [name], freeVariables body \\ (args ++ explicitlyTyped))
                                         | (i, (name, args, body)) <- zip [1,3..] fcnDefs ]
                     nodes = [(body, i, links)
                                  | (body, i, _, needed) <- simpleGroups
                                  , let links = [j | (_, j, bound, _) <- simpleGroups, not (null (needed `intersect` bound))]]
                     sccs = stronglyConnComp nodes
                 -- ... and construct the result.
                 decls' <- liftM Decls (mapM (makeTypingGroup signatures) sccs)
                 return decls'
              where -- splitPattern is responsible for distinguishing value and function bindings
                    splitPattern :: Located S.Pattern -> M (Either (Located S.Pattern) (Id, [Located S.Pattern]))
                    splitPattern p =
                        case S.flattenPattern p of
                          (At _ (S.PVar fcn), args) ->
                              return (Right (fcn, args))
                          (At _ (S.PCon name), _) ->
                              return (Left p)
                          (p, []) ->
                              return (Left p)
                          _ -> failWithS "Invalid LHS"

                    singleton = (:[])

                    -- desugarEquation actually has surprisingly little work left: we've already
                    -- distinguished value and function bindings, we've already handled binings and
                    -- replacements; all that's left is calling the desugar methods for the left-
                    -- and right-hand sides.  In the process, we attempt to desugar "value"
                    -- definitions with lambdas on the right-hand side to function definitions; this
                    -- allows recursion in definitions like:
                    --    f = \ x -> f x
                    -- which would otherwise be illegal.
                    desugarEquation :: (Either (Located S.Pattern) (Id, [Located S.Pattern]), S.Rhs)
                                    -> M (Either (Located (Pattern PredFN Id), Match PredFN Id) (Id, [Located (Pattern PredFN Id)], Match PredFN Id))
                    desugarEquation (Left p, rhs) =
                        do p' <- desugar p
                           m <- desugar rhs
                           case p' of
                             At _ (PVar name) ->
                                 case commuteLambdas m of
                                   ([], _) -> return (Left (p', m))
                                   (ps, body) -> return (Right (name, map (introduced . PVar) ps, body))
                             _ -> return (Left (p', m))
                    desugarEquation (Right (name, params), rhs) =
                        do params' <- mapM desugar params
                           body <- desugar rhs
                           return (Right (name, params', body))

                    -- We commute lambdas in two cases; either definitions of the form:
                    --   f = {^ \x -> {p <- x => m }}
                    -- or definitions of the form
                    --   f = {^ \x -> m}
                    -- Note that we won't commute a lambda past a let guard or a pattern match
                    -- against anything besides the variable in the outermost lambda.
                    commuteLambdas :: Match PredFN Id -> ([Id], Match PredFN Id)
                    commuteLambdas (MCommit (At _ (ELam v (At _ (EMatch (MGuarded (GFrom p (At l (EVar v'))) body))))))
                        | v == v' = (v:ps, MGuarded (GFrom p (At l (EVar v))) body')
                        where (ps, body') = commuteLambdas body
                    commuteLambdas (MCommit (At _ (ELam v (At _ (EMatch body))))) = (v:ps, body')
                        where (ps, body') = commuteLambdas body
                    commuteLambdas m = ([], m)

                    hasDuplicates :: Eq t => [t] -> Bool
                    hasDuplicates [] = False
                    hasDuplicates (t:ts) = t `elem` ts || hasDuplicates ts

                    -- mergeEquations is fairly simple: we iterate over the equations, tracking the
                    -- function defined in the last equation encountered (if any).  Multiple
                    -- equations defining (cases of) the same function are combined using MElse
                    -- after we check that they have the same number of parameters; value equations
                    -- are passed through unchanged.
                    mergeEquations :: [Either (Located (Pattern PredFN Id), Match PredFN Id) (Id, [Located (Pattern PredFN Id)], Match PredFN Id)]
                                   -> M [Either (Located (Pattern PredFN Id), Match PredFN Id) (Function PredFN Id)]
                    mergeEquations [] = return []
                    mergeEquations eqns = iter [] Nothing eqns
                        where iter done Nothing []                                 = return done
                              iter done (Just inProgress) []                       = return (Right inProgress : done)
                              iter done Nothing (Left (p, e) : rest)               = iter (Left (p, e) : done) Nothing rest
                              iter done (Just inProgress) (Left (p, e) : rest)     = iter (Left (p, e) : Right inProgress : done) Nothing rest
                              iter done Nothing (Right (name, params, match) : rest) =
                                  do args <- replicateM (length params) (fresh "x")
                                     iter done (Just (name, args, matchFrom args params match)) rest
                              iter done (Just (nameIP, argsIP, matchIP)) (Right (name, params, match) : rest)
                                  | nameIP == name =
                                      if length argsIP /= length params
                                      then failWithS ("Different arities in equations for " ++ fromId name)
                                      else iter done (Just (nameIP, argsIP, MElse matchIP (matchFrom argsIP params match))) rest
                                  | name `elem` [id | Right (id, _, _) <- done] =
                                      failWithS ("Redefinition of function " ++ fromId name)
                                  | otherwise =
                                      do newArgs <- replicateM (length params) (fresh "x")
                                         iter (Right (nameIP, argsIP, matchIP) : done) (Just (name, newArgs, matchFrom newArgs params match)) rest

                              matchFrom :: [Id] -> [Located (Pattern PredFN Id)] -> Match PredFN Id -> Match PredFN Id
                              matchFrom args params match = foldr (\(arg, p@(At l _)) m -> MGuarded (GFrom p (At l (EVar arg))) m) match (zip args params)

                    signatureFor :: Id -> [Signature PredFN Id] -> Maybe (Signature PredFN Id)
                    signatureFor name signatures = iter signatures
                        where iter []             = Nothing
                              iter (s@(Signature name' _) : rest)
                                  | name == name' = Just s
                                  | otherwise     = iter rest

                    singleFunctionTypingGroup :: (Id, [Id], Match PredFN Id) -> [Signature PredFN Id] -> TypingGroup PredFN Id
                    singleFunctionTypingGroup (name, params, body) signatures =
                        case signatureFor name signatures of
                          Nothing                -> Implicit [(name, params, body)]
                          Just (Signature _ tys) -> Explicit (name, params, body) tys

                    makeTypingGroup :: [Signature PredFN Id] -> SCC (Either (Located (Pattern PredFN Id), Match PredFN Id) (Function PredFN Id)) -> M (TypingGroup PredFN Id)
                    makeTypingGroup signatures (AcyclicSCC (Left (p, e))) =
                        return (Pattern p e (catMaybes [signatureFor name signatures | name <- bound p]))
                    makeTypingGroup signatures (AcyclicSCC (Right f)) =
                        return (singleFunctionTypingGroup f signatures)
                    makeTypingGroup signatures (CyclicSCC nodes) =
                        case partitionEithers nodes of
                          ([], [f])              -> return (singleFunctionTypingGroup f signatures)
                          ([], fcns)             -> return (Implicit fcns)
                          ((At loc _, _) : _, _) -> failAt loc $ failWithS "Recursive value definition"

instance Sugared S.Signature (Signature PredFN Id)
    where desugar (S.Signature id ty) =
              liftM (Signature id) (toKScheme [] [] `fmap` desugar ty)

----------------------------------------------------------------------------------------------------
-- Top level declarations

-- Both instance and class declarations have the odd invariant that their 'where' blocks can only
-- contain function definitions.  Unfortunately, the 'Decls' conversion code will interpret a
-- declaration of the form:

--   x = id

-- as a pattern binding (binding 'PVar "x"') rather than a function binding.  The following function
-- desugars pattern bindings of that form to "function" bindings, and indicates errors for any other
-- form of pattern binding.

coercePatternBinding :: String -> TypingGroup PredFN Id -> M (Functions PredFN Id)
coercePatternBinding _ (Pattern (At _ (PVar s)) m _) = return ([(s, [], m)])
coercePatternBinding _ (Explicit f _ )               = return [f]
coercePatternBinding _ (Implicit fs)                 = return fs
coercePatternBinding s _                             = failWithS s

-- Another common pattern in many top level declarations, including classes, type synonyms,
-- datatypes, etc., is that we parse the LHS of the definition as a type (to allow for infixity,
-- parenthesization, and various other forms of pathological code) but require that it fit a
-- stricter pattern (something applied to a set of (possibly kinded) type variables).  This function
-- serves two roles in that conversion: first, it maps type arguments from 'Type's to 'TyParam's,
-- and second, looks for duplicate parameters in the process.

validateTypeParameter :: Located (Type Id) -> [Located (Either KId Id)] -> M [Located (Either KId Id)]
validateTypeParameter arg args =
    case arg of
      At loc (TyVar v)
          | v `elem` map paramName args' -> failAt loc $ failWithS ("Duplicate class parameter name '" ++ fromId v ++ "'")
          | otherwise                    -> return (At loc (Right v) : args)
      At loc (TyKinded (At _ (TyVar v)) (At _ k))
          | v `elem` map paramName args' -> failAt loc $ failWithS ("Duplicate class parameter name '" ++ fromId v ++ "'")
          | otherwise                    -> return (At loc (Left (Kinded v k)) : args)
      At loc _                           -> failAt loc $ failWith (text "Unexpected class parameter" <+> ppr arg)
    where args' = map dislocate args

typeFromTypeParameter :: Located (Either KId Id) -> Located (Type Id)
typeFromTypeParameter (At l (Left (Kinded id k))) = At l (TyKinded (At l (TyVar id)) (At l k))
typeFromTypeParameter (At l (Right id))           = At l (TyVar id)

desugarClassConstraints :: Id -> [Located (Either KId Id)] -> [Located S.ClassConstraint] -> M ([Located ClassConstraint], [Top])
desugarClassConstraints className params constraints = partitionEithers `fmap` mapM desugar' constraints
    where desugar' (At loc (S.Superclass p)) =
              do n <- fresh "super"
                 p' <- desugar p
                 return (Right (Require [(n, At loc p')] [At loc (PredFN className (map typeFromTypeParameter params) Nothing Holds)]))
          desugar' (At loc (S.Fundep fd)) =
              do (At _ fd') <- desugarFunctionalDependency params (At loc fd)
                 return (Left (At loc (Fundep fd')))
          desugar' (At loc (S.Opaque v)) =
              case findIndex (v ==) names of
                Nothing -> failWithS "Invalid parameter name in opacity constraint"
                Just i  -> return (Left (At loc (Opaque i)))
              where names = map (paramName . dislocate) params

desugarFunctionalDependency :: [Located (Either KId Id)] -> Located (Fundep Id) -> M (Located (Fundep Int))
desugarFunctionalDependency params (At loc (xs :~> ys)) =
    failAt loc $
    case (xs', ys') of
      (Just xs', Just ys') -> return (At loc (xs' :~> ys'))
      _ -> failWithS "Invalid parameter name in functional dependency constraint"
    where names = map (paramName . dislocate) params
          toIdx s = findIndex (s ==) names
          xs' = mapM toIdx xs
          ys' = mapM toIdx ys

-- We don't want to use the default implementation of desugar for method signatures because we don't
-- want to quantify over class parameters; e.g., in the definition
--   class Eq t where (==) :: t -> t -> Bool
-- =='s type should remain t -> t -> Bool, not forall k. _0 -> _0 -> Bool.
desugarMethodSignature ps (S.Signature name qty) = Signature name `fmap` (toKScheme pkvars pvars `fmap` desugar qty)
    where pkvars = K.vars ps
          pvars  = map (paramName . dislocate) ps

type Top = TopDecl PredFN Id (Either KId Id)

instance Sugared S.Class [Top]
    where desugar (S.Class ty determined constraints mdecls) =
              do ty' <- desugar ty
                 case flattenType ty' of
                   (At _ (TyCon name), []) ->
                       failWithS "Class without parameters is pointless"
                   (At _ (TyCon name), params) ->
                       do params' <- case determined of
                                       Nothing -> return params
                                       Just t  -> do t' <- desugar t
                                                     return (params ++ [t'])
                          params'' <- foldrM validateTypeParameter [] params'
                          (constraints', requirements) <- desugarClassConstraints name params'' constraints
                          let n             = length params''
                              constraints'' = case determined of
                                                Nothing         -> constraints'
                                                Just (At loc _) -> At loc (Fundep ([0..n - 2] :~> [n - 1])) : constraints'
                          (methods, defaults) <-
                              case mdecls of
                                Nothing -> return ([], [])
                                Just decls ->
                                    do let defaultNames      = concatMap lhsBound [lhs | lhs S.:= _ <- S.equations decls]
                                           defaultSignatures = [s | s@(S.Signature name _) <- S.signatures decls, name `elem` defaultNames]
                                           methodNames       = [name | S.Signature name _ <- S.signatures decls]
                                       defaultDecls <- desugar decls { S.signatures = defaultSignatures }
                                       defaults     <- concatMapM (coercePatternBinding "Class method defaults must be functions")
                                                                  (groups defaultDecls)
                                       when (any (`notElem` methodNames) defaultNames) $
                                            failWithS ("Default implementation for non-class method: " ++ intercalate ", " (map fromId (filter (`notElem` methodNames) defaultNames)))
                                       signatures' <- mapM (desugarMethodSignature params'') (S.signatures decls)
                                       return (signatures', defaults)
                          return (Class name params'' constraints'' methods defaults : requirements)
                   _ -> failWithS "Invalid class LHS (must be a class name applied to a list of parameters)"

              where lhsBound :: Located S.Pattern -> [Id]
                    lhsBound p = case S.flattenPattern p of
                                   (At loc (S.PVar name), [])   -> [name]
                                   (At loc (S.PVar fcn), args)  -> [fcn]
                                   (At loc (S.PCon name), args) -> concatMap bound args
                                   (p, [])                      -> bound p

instance Sugared S.Instance (Top, [Primitive PredFN Id])
    where desugar (S.Instance chain) =
              do name <- fresh "i"
                 (chain', topDecls) <- unzip `fmap` mapM desugar' chain
                 let (cl:cls) = [name | (_ :=> At _ (PredFN name _ _ _), _) <- chain']
                 if all (cl ==) cls
                    then return (Instance name cl chain', catMaybes topDecls)
                    else failWithS "Instance refers to different classes"

              where desugar' (qs S.:=> At l1 (S.Pred t (Just (At l2 S.TyWild)) Holds), mdecls) =
                        do name <- fresh "T"
                           ((qp', decls), _) <- desugar' (qs S.:=> At l1 (S.Pred t (Just (At l2 (S.TyCon name))) Holds), mdecls)
                           return ((qp', decls), Just (PrimType name (KVar name)))

                    desugar' (qp, mdecls) =
                        do qp' <- desugar qp
                           decls <- maybe (return emptyDecls) desugar mdecls
                                    >>= (concatMapM (coercePatternBinding "Instance methods must be functions") . groups)
                           return ((qp', decls), Nothing)

instance Sugared S.Requirement Top
    where desugar (S.Require ps qs) =
              do names <- replicateM (length ps) (fresh "require")
                 ps <- mapM desugar ps
                 Require (zip names ps) `fmap` mapM desugar qs

desugarInterface :: Id -> [Located (Either KId Id)] -> [Located (PredType PredFN Id)] -> Located (Type Id) -> S.Decls -> M [Top]
desugarInterface name params rhsPreds rhsType interface =
    do instName <- fresh "opaque"
       Decls ds <- desugar interface
       signatures <- mapM (desugarMethodSignature params) (S.signatures interface)
       case mapM fromTypingGroup ds of
         Nothing ->
             failWithS ("Unexpected declaration in opaque type interface")
         Just impls ->
             let cl = Class name
                            (params ++ [introduced (Right "t$")])
                            [introduced (Fundep ([0..n-1] :~> [n])), introduced (Fundep ([n] :~> [0..n-1])), introduced (Opaque n)]
                            signatures
                            []
                 inst = Instance instName name
                                 [(rhsPreds :=> introduced (PredFN name (map typeFromTypeParameter params ++ [rhsType]) Nothing Holds), impls)]
             in return [cl, inst]
    where n = length params
          fromTypingGroup (Explicit impl@(id, _, _) _) =
              Just impl
          fromTypingGroup _ =
              Nothing

instance Sugared S.Synonym [Top]
    where desugar (S.Synonym lhs rhs interface) =
              do lhs' <- desugar lhs
                 ps :=> t <- desugar rhs
                 case flattenType lhs' of
                   (At _ (TyCon name), params) ->
                       do params' <- foldrM validateTypeParameter [] params
                          case interface of
                            Nothing ->
                                do instName <- fresh "synonym"
                                   let n          = length params'
                                       vs         = tvs t
                                       determined = catMaybes (map (findParam 0 params') vs)
                                       fds | null determined = [introduced (Fundep ([0..n - 1] :~> [n]))]
                                           | otherwise       = [introduced (Fundep ([n] :~> determined)), introduced (Fundep ([0..n - 1] :~> [n]))]
                                       cl         = Class name (params' ++  [introduced (Right "$t")])
                                                               fds [] []
                                       v          = introduced (TyVar "$t")
                                       inst       = Instance instName name
                                                             [(ps :=> introduced (PredFN name (map typeFromTypeParameter params' ++ [t]) Nothing Holds), []),
                                                              ([] :=> introduced (PredFN name (map typeFromTypeParameter params' ++ [v]) Nothing Fails), [])]
                                   return [cl, inst]
                            Just ds ->
                                desugarInterface name params' ps t ds
                   _ -> failWithS "Invalid synonym LHS"
              where findParam _ [] _ = Nothing
                    findParam n (At _ (Left (Kinded id _)) : rest) id'
                        | id == id'  = Just n
                        | otherwise  = findParam (n + 1) rest id'
                    findParam n (At _ (Right id) : rest) id'
                        | id == id'  = Just n
                        | otherwise  = findParam (n + 1) rest id'


-- TODO: generalizing over one (1) case here...
desugarCtor :: (Sugared p p', Sugared t t', HasTypeVariables p' Id, HasTypeVariables t' Id) =>
               [Id] -> Ctor Id p t -> M (Ctor Id p' t')
desugarCtor enclosing (Ctor name _ quals fields) =
    do quals' <- mapM desugar quals
       fields' <- mapM desugar fields
       let vs = filter (`notElem` enclosing) (nub (concatMap tvs quals' ++ concatMap tvs fields'))
       return (Ctor name vs (gen 0 vs quals') (gen 0 vs fields'))

instance Sugared S.Datatype [Top]
    where desugar (S.Datatype lhs ctors drv interface) =
              do lhs' <- desugar lhs
                 case flattenType lhs' of
                   (At loc (TyCon name), params) ->
                       do params' <- foldrM validateTypeParameter [] params
                          let pnames = map (paramName . dislocate) params'
                          ctors' <- mapM (desugarCtor pnames) ctors
                          case interface of
                            Nothing -> return [Datatype name params' ctors' drv]
                            Just ds -> do name' <- fresh name
                                          let rhs = foldl (\t p -> at t (TyApp t (typeFromTypeParameter p))) (At loc (TyCon name')) params'
                                          topDecls' <- desugarInterface name params' [] rhs ds
                                          return (Datatype name' params' ctors' drv : topDecls')
                   _ -> failWithS "Invalid datatype LHS"

instance Sugared S.DataField (Type Id)
    where desugar (S.DataField _ (At l t)) = desugar t

toMaybeScheme = maybe Nothing (Just . toScheme [])

unzipLocated :: [Located (a, b)] -> ([Located a], [b])
unzipLocated lps = (as, map dislocate bs)
    where (as, bs) = unzipLocated' lps

unzipLocated' :: [Located (a, b)] -> ([Located a], [Located b])
unzipLocated' lps = unzip [(At p t, At p u) | At p (t, u) <- lps]

type Init t = (Id, t, Located (Expr PredFN Id))

desugarCtorWithInit :: (Sugared t (t', Maybe (Init (Located (Type Id)))), HasTypeVariables t' Id)
                    => [Id] -> Ctor Id S.Pred t -> M (Ctor Id (PredType PredFN Id) t', [Init (KScheme (Scheme PredFN Id))])
desugarCtorWithInit enclosing (Ctor name _ quals fields) =
    do quals' <- mapM desugar quals
       (fields', minits) <- unzipLocated `fmap` mapM desugar fields
       let vs = filter (`notElem` enclosing) (nub (concatMap tvs quals' ++ concatMap tvs fields'))
           inits = catMaybes minits
       let initTyss = map (\(_, ty, _) -> toKScheme [] [] (quals' :=> ty)) inits
       return (Ctor name vs (gen 0 vs quals') (gen 0 vs fields'), [(id, tys, e) | ((id, _, e), tys) <- zip inits initTyss])

instance Sugared S.Bitdatatype (Top, [TypingGroup PredFN Id])
    where desugar (S.Bitdatatype name size ctors drv) =
              do size' <- toMaybeScheme `fmap` desugar size
                 (ctors', inits) <- unzip `fmap` mapM (desugarCtorWithInit []) ctors
                 return (Bitdatatype name size' ctors' drv,
                         [Explicit (v, [], MCommit e) tys | (v, tys, e) <- concat inits])

instance Sugared S.BitdataField (BitdataField Id, Maybe (Id, Located (Type Id), Located (Expr PredFN Id)))
    where desugar (S.LabeledField name ty Nothing) =
              do ty' <- desugar ty
                 return (LabeledField name ty' Nothing, Nothing)
          desugar (S.LabeledField name ty (Just (At loc init))) =
              do v <- fresh "init"
                 ty' <- desugar ty
                 init' <- desugar init
                 return (LabeledField name ty' (Just v), Just (v, ty', At loc init'))
          desugar (S.ConstantField lit) =
              return (ConstantField lit, Nothing)

instance Sugared S.Struct (Top, [TypingGroup PredFN Id])
    where desugar (S.Struct name size ctor drv) =
              do size' <- toMaybeScheme `fmap` desugar size
                 (ctor', inits) <- desugarCtorWithInit [] ctor
                 return (Struct name size' ctor' drv,
                         [Explicit (v, [], MCommit e) tys | (v, tys, e) <- inits])

instance Sugared S.StructRegion (StructRegion Id, Maybe (Id, Located (Type Id), Located (Expr PredFN Id)))
    where desugar (S.StructRegion Nothing ty) =
              do ty' <- desugar ty
                 return (StructRegion Nothing ty', Nothing)

          desugar (S.StructRegion (Just field) ty) =
              do (field', init') <- desugar field
                 ty'@(At loc _) <- desugar ty
                 let init'' = do (id, e) <- init'
                                 return (id, At loc (TyApp (At loc (TyCon "Init")) ty'), e)
                 return (StructRegion (Just field') ty', init'')

instance Sugared S.StructField (StructField, Maybe (Id, Located (Expr PredFN Id)))
    where desugar (S.StructField name Nothing) = return (StructField name Nothing, Nothing)
          desugar (S.StructField name (Just (At loc init))) =
              do v <- fresh "init"
                 init' <- desugar init
                 return (StructField name (Just v), Just (v, At loc init'))

instance Sugared S.Area (Top, [TypingGroup PredFN Id])
    where desugar (S.Area v namesAndInits ty mdecls) =
              do qty@(ps :=> t) <- desugar ty
                 let tys    = toScheme [] qty
                     initTy = toKScheme [] [] (ps :=> introduced (TyApp (introduced (TyCon "Init"))
                                                                        (introduced (TyApp (introduced (TyCon "AreaOf")) t))))
                 Decls groups <-
                     case mdecls of
                       Nothing -> return (Decls [])
                       Just decls -> desugar decls
                 (ps, inits) <- unzip `fmap` mapM rewriteInit namesAndInits
                 return ( Area v ps tys
                        , groups ++ [Explicit (v, [], MCommit e) initTy | (v, e) <- inits] )

              where rewriteInit (At loc name, Nothing) =
                        do v <- fresh "init"
                           return ((At loc name, v), (v, At loc (EVar "initialize")))
                    rewriteInit (name, Just init) =
                        do v <- fresh "init"
                           init' <- desugar init
                           return ((name, v), (v, init'))

----------------------------------------------------------------------------------------------------
-- Primitives

validatePrimitiveTypeParameter :: Located (Either KId Id) -> M (Located KId)
validatePrimitiveTypeParameter (At l (Right _)) = failAt l $ failWithS "All arguments to primitive types and classes must have kind annotations"
validatePrimitiveTypeParameter (At l (Left id)) = return (At l id)

instance Sugared S.Primitive (Either (Signature PredFN Id, String) (Primitive PredFN Id))
    where desugar (S.PrimValue s name _) =
              do s' <- desugar s; return $ Left (s', name)
          desugar (S.PrimCon s name _) =
              do s' <- desugar s; return (Right (PrimCon s' name))
          desugar (S.PrimType lhs) =
              Right `fmap`
              do lhs' <- desugar lhs
                 case flattenType lhs' of
                   (At _ (TyCon name), params) ->
                       do params' <- mapM validatePrimitiveTypeParameter =<< foldrM validateTypeParameter [] params
                          return (PrimType name (foldr KFun KStar (map (kind . dislocate) params')))
                   (At _(TyKinded (At _ (TyCon name)) (At _ k)), []) ->
                             return (PrimType name k)
                   _ -> failWithS "Invalid primitive type declaration"
          desugar (S.PrimClass lhs determined constraints mdecls) =
              Right `fmap`
              do lhs' <- desugar lhs
                 case flattenType lhs' of
                   (At _ (TyCon _), []) ->
                       failWithS "Primitive class without parameters is primitively pointless"
                   (At _ (TyCon name), params) ->
                       do params' <- case determined of
                                       Nothing -> return params
                                       Just t  -> do t' <- desugar t
                                                     return (params ++ [t'])
                          params'' <- mapM validatePrimitiveTypeParameter =<< foldrM validateTypeParameter [] params'
                          let eitheredParams = map (fmap Left) params''
                          constraints' <- mapM (desugarFunctionalDependency eitheredParams) constraints
                          let n             = length params''
                              constraints'' = case determined of
                                                Nothing         -> constraints'
                                                Just (At loc _) -> At loc ([0..n - 2] :~> [n - 1]) : constraints'
                          methods <-
                              case mdecls of
                                Nothing -> return []
                                Just decls ->
                                    do when (not (null (S.equations decls))) $ failWithS "Unexpected default method in primitive class declaration"
                                       mapM (desugarMethodSignature eitheredParams) (S.signatures decls)
                          return (PrimClass name params'' constraints'' methods)

----------------------------------------------------------------------------------------------------
-- Desugaring programs

-- The one complication here is that we need to know the order of bitdata fields when desugaring
-- patterns.  Therefore, we start by collecting fields from each bitdata ctor; afterwards, we can
-- map 'desugar' across the program structure as usual.

type DesugaringState = ([(Id, Id)], CtorEnv)

desugarProgram :: Has s DesugaringState => Pass s S.Program (Program PredFN Id (Either KId Id))
desugarProgram = up (\p -> PassM (StateT (f p)))
    where f p globals = runReaderT (runM (convertProgram p globals)) ([], [])

          pushLocationInwards :: Located [t] -> [Located t]
          pushLocationInwards (At l ts) = map (At l) ts

          typeDeclNames :: [Located Top] -> [Located Id]
          typeDeclNames = catMaybes . map nameFrom
              where nameFrom (At l (Datatype name _ _ _))    = Just (At l name)
                    nameFrom (At l (Bitdatatype name _ _ _)) = Just (At l name)
                    nameFrom (At l (Struct name _ _ _))      = Just (At l name)
                    nameFrom (At l (Area {}))                = Nothing
                    nameFrom (At l (Class name _ _ _ _))     = Just (At l name)
                    nameFrom (At l (Instance {}))            = Nothing

          primitiveTypeNames = catMaybes . map nameFrom
              where nameFrom (At l (PrimType name _))      = Just (At l name)
                    nameFrom (At l (PrimClass name _ _ _)) = Just (At l name)

          tyconName :: Located S.Type -> M Id
          tyconName ty = do ty' <- desugar ty
                            case flattenType ty' of
                              (At _ (TyCon name), _) -> return name
                              _                      -> error ("tyconName (" ++ show (ppr ty) ++ ")")

          convertProgram :: S.Program -> DesugaringState -> M (Program PredFN Id (Either KId Id), DesugaringState)
          convertProgram p (globalMethodNames, (globalBitCtors, globalStructCtors)) =
              bindCtors (bitCtorNames, structCtorNames) $
              do Decls values <- desugar (S.decls p)
                 methodNames' <- (++ globalMethodNames) `fmap`
                                 mapM (\(lhs, m) -> do name <- tyconName lhs; return (name, m))
                                 methodNames
                 classesAndSupers <- (concat . map pushLocationInwards) `fmap` mapM desugar (S.classes p)
                 (instances, instPrimTypes) <- unzipLocated' `fmap` mapM desugar (S.instances p)
                 requirements <- mapM desugar (S.requirements p)
                 synonyms <- (concat . map pushLocationInwards) `fmap` mapM desugar (S.synonyms p)
                 datatypes <- (concat . map pushLocationInwards) `fmap` mapM desugar (S.datatypes p)
                 (bitdatatypes, bitdataInits) <- unzipLocated `fmap` mapM desugar (S.bitdatatypes p)
                 (structures, structureInits) <- unzipLocated `fmap` mapM desugar (S.structures p)
                 (areas, areaInits) <- unzipLocated `fmap` mapM desugar (S.areas p)
                 primitives <- mapM desugar (S.primitives p)

                 let primitiveTypesAndClasses = [At t p | At t (Right p) <- primitives]
                     primitiveValues = [PrimValue p s | At t (Left (p, s)) <- primitives]
                     topDecls = classesAndSupers ++ instances ++ requirements ++ synonyms ++ datatypes ++ bitdatatypes ++ structures ++ areas

                 rejectDuplicates locatedCtorNames

                 return (Program (Decls (values ++ concat bitdataInits ++ concat structureInits ++ concat areaInits ++ primitiveValues))
                                 topDecls
                                 (primitiveTypesAndClasses ++ concat (map pushLocationInwards instPrimTypes))
                        , (methodNames', (bitCtorNames, structCtorNames)))

              where bitCtorNames    = [(name, nullary fields) | At _ (S.Bitdatatype _ _ ctors _) <- S.bitdatatypes p,
                                                                Ctor (At _ name) _ _ fields <- ctors]
                                      ++ globalBitCtors
                    nullary fields  = null [n | At _ (S.LabeledField n _ _) <- fields]

                    structCtorNames = [name | At _ (S.Struct _ _ (Ctor _ _ _ regions) _) <- S.structures p,
                                              At _ (S.StructRegion (Just (S.StructField (At _ name) _)) _) <- regions]
                                      ++ globalStructCtors

                    methodNames =
                        [(classLHS, id) | At _ (S.Class classLHS _ _ (Just ds)) <- S.classes p, S.Signature id _ <- S.signatures ds] ++
                        [(classLHS, id) | At _ (S.PrimClass classLHS _ _ (Just ds)) <- S.primitives p, S.Signature id _ <- S.signatures ds]
                    allMethodNames = map snd methodNames ++ map snd globalMethodNames
                    locatedCtorNames =
                        concat ([map ctorName ctors | At _ (S.Datatype _ ctors _ _) <- S.datatypes p] ++
                                [map ctorName ctors | At _ (S.Bitdatatype _ _ ctors _) <- S.bitdatatypes p])
                    ctorNames = map dislocate locatedCtorNames
                    areaNames =
                        concat [map dislocate (fst (unzip inits)) | At _ (S.Area _ inits _ _) <- S.areas p]
                    primitiveNames =
                        [id | At _ (S.PrimValue (S.Signature id _) _ _) <- S.primitives p]
                    primitiveNamesAndVisibilities =
                        [(id, visible) | At _ (S.PrimValue (S.Signature id _) _ visible) <- S.primitives p]

-- TODO: consider rewording the text of the error message produced by this function so that it fits
-- with all uses.
rejectDuplicates :: [Located Id] -> M ()
rejectDuplicates ids =
    case duplicates ids of
      [] -> return ()
      ds -> failWithS (unlines [fromId id ++ " appears at both " ++ show l ++ " and " ++ show l' | (id, l, l') <- ds])
    where duplicates :: [Located Id] -> [(Id, Location, Location)]
          duplicates [] = []
          duplicates (At l id : rest) =
              case locateDuplicate id rest of
                Just l' -> (id, l, l') : rest'
                _       -> rest'
              where rest' = duplicates rest
                    locateDuplicate _ [] = Nothing
                    locateDuplicate id (At l id' : rest)
                        | id == id' = Just l
                        | otherwise = locateDuplicate id rest
