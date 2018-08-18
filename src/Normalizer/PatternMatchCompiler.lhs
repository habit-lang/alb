Pattern Match Compilation:
--------------------------

This file describes the translation of XMPEG programs into LambdaCase.  We
refer to this process as "pattern match compilation" because it eliminates
the richeness of XMPEG pattern matching, including guards and backtracking
on failure, in favor of a language that provides only simple case expressions
and a limited fatbar operator.  This process is accomplished by a conceptual
translation of XMPEG programs into the "Match Normal Form" that is described
in the compiler report from November 2010.

TODO:

- how to handle pattern bindings?

> {-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, MultiParamTypeClasses, NamedFieldPuns, OverloadedStrings, TupleSections #-}
> module Normalizer.PatternMatchCompiler(patternMatch) where

> import Common hiding (fresh)
> import qualified Common as C
> import Control.Monad (liftM2, replicateM)
> import Control.Monad.State
> import Data.Maybe
> import Syntax.Specialized as X
> import Syntax.LambdaCase as LC
> import Syntax.LambdaCase.SCC
> import qualified Utils.BDD as BDD


ENTRY POINT:

Pattern matching is a compiler pass that uses the global Int counter to
allow the generation of fresh variable names.


> patternMatch :: Pass () X.Specialized LC.Program
> patternMatch (Specialized topDecls entry decls) =
>     liftBase (do decls' <- pmcDecls [] decls
>                  return (LC.Program (sccDecls decls')
>                                     (lcTopDecls topDecls)))

Pattern match compilation runs in a monad called PMC that supports the
generation of fresh names:

> type PMC = Base

> fresh :: PMC Id
> fresh  = C.fresh "v"

UTILITIES:

Pattern match compilation requires simple renamings/substitutions to
track variable bindings.  For example, one step in converting a LambdaCase
equivalent of the XMPEG term:

    (C x y <- p => m1)
  | (C u v <- p => m2)

is to rename the two branches:

    (C a b <- p => [a/x, b/y]m1)
  | (C a b <- p => [u/x, v/y]m2)

so that the guard portions are the same, allowing us to use distributivity,
Law (11), to obtain:

    C a b <- p => ( [a/x, b/y]m1
                  | [u/x, v/y]m2)

(The pattern here, in which different alternatives have different substitutions,
is common in practice and motivates the use of the SMS type that is defined below.)

We represent these substitutions as association lists:

> type Subst = [(Id, Id)]    -- each pair (v, w) represents renaming of v +> w

> extend        :: [Id] -> [Id] -> Subst -> Subst -- domain, range, base, result
> extend is vs s = zip is vs ++ s

> applySubst    :: Subst -> Id -> Id
> applySubst s i = fromMaybe i (lookup i s)

We also provide some helper functions for manipulating pieces of abstract syntax:

> -- Create a binding for (i :: t; i=e)
> simpleLet       :: Id -> X.Type -> X.Expr -> X.Guard
> simpleLet i t e  = X.GLet (X.Decls [val])
>  where val = X.Defn i (X.Forall [] [] t) (Right (X.Gen [] [] e))

> -- Create a variable from an identifier, type unknown
> evar            :: Id -> LC.Expr
> evar w           = (LC.EVar w typeNotKnown)

> typeNotKnown :: LC.Type
> typeNotKnown  = LC.TyLabel "not known"


PATTERN MATCH COMPILATION:

Pattern match compilation of a list of XMPEG declarations results in a
corresponding set of LambdaCase declarations.  LambdaCase requires lists of
declarations to be partitioned into binding groups, each of which is marked
appropriately as either Mutual or Nonrec.  This code ignores that distinction,
translating each group of Functions into a single Mutual block and relying on
a post-processing phase using sccDecls to establish the correct binding group
structure.

> pmcDecls                :: Subst -> X.Decls -> PMC LC.Decls
> pmcDecls s (X.Decls defns) = do defns' <- mapM toDefn defns
>                                 return (LC.Decls [Mutual defns'])
>  where toDefn                 :: X.Defn -> PMC LC.Defn
>        toDefn (X.Defn i (X.Forall [] [] t) (Left (id, ts)))
>                                = LC.Defn i (convert t) `fmap` return (Left (id, convert ts))
>        toDefn (X.Defn i (X.Forall [] [] t) (Right (X.Gen [] [] e)))
>                                = (LC.Defn i (convert t) . Right) `fmap` pmcExpr s e

Pattern match compilation of an XMPEG expression produces a LambdaCase
expression.  For the most part, this is a simple walk over the abstract
syntax, applying the current substitution at appropriate points.  The numbers
(n) attached as comments in this code reference the laws for manipulating MPEG
expressions in the November 2010 document about the front-end of the compiler.
(Some of the laws are not used here, either because they cover cases that do
not appear in the already simplified form of XMPEG syntax that is passed in as
as here, or else because they have more to do with defining semantics or
runtime behavior/semantics.  We specifically do not use Law 10 so as to
preserve the order in which constructors are listed in the original program.

> pmcExpr                                 :: Subst -> X.Expr -> PMC LC.Expr
> pmcExpr s (X.ELamVar i)                  = return (evar (applySubst s i))
> pmcExpr s (X.ELetVar (X.Inst i ts []))   = error $ "PatternMatchCompiler:36.5:" ++ fromId i
> pmcExpr s (X.EBits bits size)            = return (LC.EBits bits size)
> pmcExpr s (X.ECon (Inst i ts _))         = return (LC.ECon i (map convert ts) typeNotKnown)
> pmcExpr s (X.EBitCon id es)              = LC.EBitCon id `fmap`
>                                              mapM (\(f, e) -> (f,) `fmap` pmcExpr s e) es
> pmcExpr s (X.ELam i t e)                 = LC.ELam i (convert t) `fmap` pmcExpr s e
> pmcExpr s (X.ESubst {})                  = error "PatternMatchCompiler:37"
> pmcExpr s (X.EMethod {})                 = error "PatternMatchCompiler:38"
> pmcExpr s (X.EApp f x)                   = liftM2 LC.EApp (pmcExpr s f) (pmcExpr s x)
> pmcExpr s (X.EBitSelect e f)             = flip LC.EBitSelect f `fmap` pmcExpr s e
> pmcExpr s (X.EBitUpdate e f e')          = liftM3 LC.EBitUpdate (pmcExpr s e)
>                                                                 (return f)
>                                                                 (pmcExpr s e')
> pmcExpr s (X.EMatch (X.MCommit e))       = pmcExpr s e      -- (4)
> pmcExpr s (X.EMatch m)                   = pmcMatch s m
> pmcExpr s (X.ELet ds e)                  = liftM2 LC.ELet (pmcDecls s ds) (pmcExpr s e)
> pmcExpr s (X.EStructInit k fs)           = LC.EStructInit k `fmap`
>                                               mapM (\(f, e) -> (f,) `fmap` pmcExpr s e) fs
> pmcExpr s (X.EBind ta _ _ _ v e e1)      = liftM2 (LC.EBind v (convert ta))
>                                                   (pmcExpr s e)
>                                                   (pmcExpr s e1)
> pmcExpr s (X.EReturn e)                  = fmap LC.EReturn (pmcExpr s e)

Pattern match compilation of an XMPEG Match produces a single LambdaCase
expression.  Our implementation proceeds in three steps:

1) Break the original match into a list of (substitution, match) pairs where
   each match is either guarded by a GLet, or guarded by a GFrom of the form
   (Con vars <- var), or else is an MCommit (but only at the end of the list)

2) Generate a sequence of LambdaCase expressions grouping adjacent GFrom
   entries from Step (1) where possible to form maximal case blocks.

3) Combine the list of LambdaCase expressions by inserting fatbars between
   the expressions.

> type SMS       = [(Subst, X.Match)]

> pmcMatch      :: Subst -> X.Match -> PMC LC.Expr
> pmcMatch s m   = pmcMatches [(s,m)]

> pmcMatches    :: SMS -> PMC LC.Expr
> pmcMatches sms = foldr1 LC.EFatbar `fmap`
>                   (normalizeMatches sms >>= groupMatches)

The normalizeMatches function implements Step 1 described above.  This task
is eased by the fact that some of the transformations that we might need to
make here have already been performed in earlier stages of the front end.  In
particular:

- The arguments of constructor pattern (PCon) are variables, so we do not have
  to account for nested patterns (although the algorithm described here could
  be extended to handle that possibility).

- The right hand side of each GFrom is guaranteed to be a variable.  (If this
  had not already been done, then we could establish it here by using Law (16)
  from the compiler report.)

The implementation of normalizeMatches uses local functions to implement a
state machine that tracks the form of the XMPEG expression that is being
normalized.

> normalizeMatches            :: SMS -> PMC SMS
> normalizeMatches []          = return []
> normalizeMatches ((s,m):sms) = normMatch s m sms
>  where

>   -- Normalize a match of the form s m | sms
>   normMatch                       :: Subst -> X.Match -> SMS -> PMC SMS
>   normMatch s (X.MElse m n)    sms = normMatch s m ((s,n):sms) -- (9)
>   normMatch s X.MFail          sms = normalizeMatches sms      -- (6)
>   normMatch s (X.MCommit e)    sms = return [(s, X.MCommit e)] -- (3)
>   normMatch s (X.MGuarded g m) sms = normGuard s g m sms       -- ==

>   -- Normalize a match of the form s (g => m) | sms
>   normGuard                       :: Subst -> X.Guard -> X.Match -> SMS -> PMC SMS
>   normGuard s (X.GFrom p e) m sms  = normFrom s p e m sms      -- ==
>   normGuard s g@(X.GLet ds) m sms
>                    | emptyDecls ds = normMatch s m sms         -- ==
>                    | otherwise     = ((s, X.MGuarded g m):)    -- eval block
>                                      `fmap` normalizeMatches sms
>   normGuard _ (X.GSubst _)  _ _    = error "GSubst in PatternMatchCompiler"
>   normGuard _ (X.GLetTypes _) _ _  = error "GLetTypes in PatternMatchCompiler"


>   -- Normalize a match of the form s ((p <- e) => m) | sms
>   normFrom :: Subst -> X.Pattern -> X.Id -> X.Match -> SMS -> PMC SMS
>   normFrom s X.PWild w m sms
>     = normMatch s m sms                         -- ((_ <-e) => m) == m

>   normFrom s (X.PVar v t) w m sms
>     = normMatch (extend [v] [applySubst s w] s) m sms  -- (1)

>   normFrom s p@(X.PCon _ _) w m sms
>     = do m' <- rebuild p w m
>          ((s, m'):) `fmap` normalizeMatches sms                -- case block
>       where rebuild p e m = return (X.MGuarded (X.GFrom p e) m)

Step 2 converts a sequence of XMPEG matches into LambdaCase expressions by
grouping together adjacent matches of the form  (C vs <- w) => m that use the
same variable.

> groupMatches            :: SMS -> PMC [LC.Expr]
> groupMatches []          = return []
> groupMatches ((s,m):sms) = group s m sms
>  where
>   -- Break a list of normalized matches into a sequence of case
>   -- blocks and evaluation blocks, perhaps with a trailing commit.
>   group                         :: Subst -> X.Match -> SMS -> PMC [LC.Expr]

>   group s (X.MCommit e) sms
>      = do e' <- pmcExpr s e
>           return [e']                                          -- (4)

>   group s (X.MGuarded (X.GLet ds) m) sms
>      = do ds' <- pmcDecls s ds
>           e'  <- pmcMatch s m
>           ((LC.ELet ds' e'):) `fmap` groupMatches sms

>   group s (X.MGuarded (X.GFrom (X.PCon (X.Inst c ts []) vs) w) m) sms
>      = gather (applySubst s w) (insert s (c, ts) vs m []) sms

>   group s m sms
>      = error "match not in normal form"

>   -- Gather matches that are part of a case block for a specific
>   -- variable into a case table.
>   gather                     :: Id -> CaseTable -> SMS -> PMC [LC.Expr]
>   gather w tab ((s, X.MGuarded (X.GFrom (X.PCon (X.Inst c ts []) vs) w') m):sms) | applySubst s w'==w
>                               = gather w (insert s (c, ts) vs m tab) sms
>   gather w tab sms            = do expr <- makeCase w tab
>                                    (expr:) `fmap` groupMatches sms

The code above organizes sequences of adjacent case matches into a CaseTable
data structure that can be translated into a LambdaCase case expression.

> -- Definitions of CaseTable data structures:
> type CaseTable = [(CFun, [CaseAlt])]
> type CaseAlt   = ([Id], Subst, X.Match)
> type CFun      = (Id, [X.Type])

> -- Insert an alternative into case table, adding the new alternative
> -- after any existing alternative for the same constructor:
> insert             :: Subst -> CFun -> [Id] -> X.Match -> CaseTable -> CaseTable
> insert s c vs m tab = ins tab
>  where alt                  = [(vs, s, m)]

>        ins                 :: CaseTable -> CaseTable
>        ins []               = [(c, alt)]
>        ins ((d,alts):tab)
>          | fst c == fst d   = (d, alts ++ alt) : tab
>          | otherwise        = (d, alts) : ins tab

> -- Construct a case expression from a case table:
> makeCase      :: Id -> CaseTable -> PMC LC.Expr
> makeCase w tab = LC.ECase (evar w) `fmap` mapM join tab
>  where join ((c, ts), [(is, s, m)])
>           = Alt c (convert ts) is `fmap` pmcMatch s m
>        join ((c, ts), alts@((is,_,_):_))
>           = do vs <- replicateM (length is) fresh
>                Alt c (convert ts) vs `fmap`
>                  pmcMatches [  (extend is vs s, m) | (is, s, m) <- alts ]


TRANSLATION OF TOP-LEVEL DECLARATIONS:

> lcTopDecls :: X.TopDecls X.Type -> LC.TopDecls
> lcTopDecls tops
>   = concatMap lcTopDecl tops
>     where
>      lcTopDecl (X.Datatype i ts ctors)
>        = [LC.Datatype i (convert ts) [ (i, convert cs) | (i,[],[],cs) <- ctors ]]

>      lcTopDecl (X.Bitdatatype i pat constrs)
>        = [LC.Bitdatatype i (BDD.width pat) (map bcons constrs)]
>          where bcons (i, bfields, _)
>                  = (i, map bfield bfields)
>                bfield (X.LabeledField name ty pat offset)
>                  = LC.LabeledField name (convert ty) (BDD.width pat) offset
>                bfield (X.ConstantField value pat offset)
>                  = LC.ConstantField value (BDD.width pat) offset

>      lcTopDecl (X.Struct i width fields)
>        = [LC.Struct i width (map sfield fields)]
>          where sfield (X.StructField id ty width offset)
>                  = LC.StructField id (convert ty) width offset

>      lcTopDecl (X.Area v ids ty size align)
>        = [LC.Area n v (evar i) ty' size align | let ty' = convert ty, (n, Inst i _ _) <- ids]
