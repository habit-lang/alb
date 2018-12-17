An XMPEG match is in normal form iff:

 - It consists of a top level series of matches (M_1 | M_2 | .. M_n)

 - Each M_i consists of a series of matches

     (C_1 x_1..x_n <- e => ^{b_1} | ... |
      C_n x_1..x_m <- e => ^{b_n})

   where each C_i is unique

> module Normalizer.Matches where

> import Data.Maybe

> import Syntax.Specialized
> import Syntax.XMPEG

> type Subst = [(Id, Id)]    -- each pair (v, w) represents renaming of v +> w

> extend        :: [Id] -> [Id] -> Subst -> Subst -- domain, range, base, result
> extend is vs s = zip is vs ++ s

> applySubst    :: Subst -> Id -> Id
> applySubst s i = fromMaybe i (lookup i s)


> normalizeProgram :: Specialized -> Specialized
> normalizeProgram (Specialized tds exports decls) =
>     Specialized tds [(pmcExpr [] e, b) | (e, b) <- exports] (pmcDecls [] decls)


> pmcDecls                :: Subst -> Decls -> Decls
> pmcDecls s (Decls defns) = Decls (map pmcDefn defns)
>  where pmcDefn d@(Defn i (Forall [] [] t) (Left (id, ts)))
>            = d
>        pmcDefn (Defn i (Forall [] [] t) (Right (Gen [] [] e)))
>            = Defn i (Forall [] [] t) (Right (Gen [] [] (pmcExpr s e)))

Pattern match compilation for expressions.  For the most part, this is a simple
walk over the abstract syntax, applying the current substitution at appropriate
points.  The numbers (n) attached as comments in this code reference the laws
for manipulating MPEG expressions in the November 2010 document about the
front-end of the compiler.  (Some of the laws are not used here, either because
they cover cases that do not appear in the already simplified form of XMPEG
syntax that is passed in as as here, or else because they have more to do with
defining semantics or runtime behavior/semantics.  We specifically do not use
Law 10 so as to preserve the order in which constructors are listed in the
original program.

> pmcExpr                                 :: Subst -> Expr -> Expr
> pmcExpr s (ELamVar i)                  = ELamVar (applySubst s i)
> pmcExpr s (ELetVar (Inst i ts []))     = error $ "PatternMatchCompiler:36.5:" ++ fromId i
> pmcExpr s (EBits bits size)            = EBits bits size
> pmcExpr s (ECon (Inst i ts es))        = ECon (Inst i ts es)
> pmcExpr s (EBitCon id es)              = EBitCon id [(f, pmcExpr s e) | (f, e) <- es]
> pmcExpr s (ELam i t e)                 = ELam i t (pmcExpr s e)
> pmcExpr s (ESubst {})                  = error "PatternMatchCompiler:37"
> pmcExpr s (EMethod {})                 = error "PatternMatchCompiler:38"
> pmcExpr s (EApp f x)                   = pmcExpr s f `EApp` pmcExpr s x
> pmcExpr s (EBitSelect e f)             = EBitSelect (pmcExpr s e) f
> pmcExpr s (EBitUpdate e f e')          = EBitUpdate (pmcExpr s e) f (pmcExpr s e')
> pmcExpr s (EMatch (MCommit e))         = pmcExpr s e      -- (4)
> pmcExpr s (EMatch m)                   = EMatch (pmcMatches [(s, m)])
> pmcExpr s (ELet ds e)                  = ELet (pmcDecls s ds) (pmcExpr s e)
> pmcExpr s (EStructInit k fs)           = EStructInit k [(f, pmcExpr s e) | (f, e) <- fs]
> pmcExpr s (EBind ta tb tm me v e e1)   = EBind ta tb tm me v (pmcExpr s e) (pmcExpr s e1)
> pmcExpr s (EReturn e)                  = EReturn (pmcExpr s e)

Normalization of an XMPEG expression.  Our implementation proceeds in three
steps:

1) Break the original match into a list of (substitution, match) pairs where
   each match is either guarded by a GLet, or guarded by a GFrom of the form
   (Con vars <- var), or else is an MCommit (but only at the end of the list)

2) Generate a sequence of matches grouping adjacent GFrom entries from Step (1)
   where possible to form maximal case blocks.

3) Combine the list of matches from 2 by inserting else's between the
   expressions.

> type SMS       = [(Subst, Match)]

> pmcMatches    :: SMS -> Match
> pmcMatches sms = foldr1 MElse $ groupMatches $ normalizeMatches sms

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

> normalizeMatches            :: SMS -> SMS
> normalizeMatches []          = []
> normalizeMatches ((s,m):sms) = normMatch s m sms
>  where

>   -- Normalize a match of the form s m | sms
>   normMatch                       :: Subst -> Match -> SMS -> SMS
>   normMatch s (MElse m n)    sms = normMatch s m ((s,n):sms) -- (9)
>   normMatch s MFail          sms = normalizeMatches sms      -- (6)
>   normMatch s (MCommit e)    sms = [(s, MCommit e)]          -- (3)
>   normMatch s (MGuarded g m) sms = normGuard s g m sms       -- ==

>   -- Normalize a match of the form s (g => m) | sms
>   normGuard                       :: Subst -> Guard -> Match -> SMS -> SMS
>   normGuard s (GFrom p e) m sms  = normFrom s p e m sms      -- ==
>   normGuard s g@(GLet ds) m sms
>                    | emptyDecls ds = normMatch s m sms       -- ==
>                    | otherwise     = (s, MGuarded g m) :     -- eval block
>                                      normalizeMatches sms
>   normGuard _ (GSubst _)  _ _    = error "Matches.lhs:129"
>   normGuard _ (GLetTypes _) _ _  = error "Matches.lhs:130"


>   -- Normalize a match of the form s ((p <- e) => m) | sms
>   normFrom :: Subst -> Pattern -> Id -> Match -> SMS -> SMS
>   normFrom s PWild w m sms
>     = normMatch s m sms                         -- ((_ <-e) => m) == m

>   normFrom s (PVar v t) w m sms
>     = normMatch (extend [v] [applySubst s w] s) m sms  -- (1)

>   normFrom s p@(PCon _ _) w m sms
>     = (s, m') : normalizeMatches sms
>       where m' = MGuarded (GFrom p w) m

Step 2 converts a sequence of XMPEG matches into normalized matches by grouping
together adjacent matches of the form (C vs <- w) => m that use the same
variable.

> groupMatches            :: SMS -> [Match]
> groupMatches []          = []
> groupMatches ((s,m):sms) = group s m sms
>  where
>   -- Break a list of normalized matches into a sequence of case
>   -- blocks and evaluation blocks, perhaps with a trailing commit.
>   group                         :: Subst -> Match -> SMS -> [Match]

>   group s (MCommit e) sms
>      = [MCommit (pmcExpr s e)]                                    -- (4)

>   group s (MGuarded (GLet ds) m) sms
>      = MGuarded (GLet (pmcDecls s ds)) (pmcMatches [(s, m)]) :
>        groupMatches sms

>   group s (MGuarded (GFrom (PCon c vs) w) m) sms
>      = gather (applySubst s w) (insert s c vs m []) sms

>   group s m sms
>      = error "match not in normal form"

>   -- Gather matches that are part of a case block for a specific
>   -- variable into a case table.
>   gather                     :: Id -> CaseTable -> SMS -> [Match]
>   gather w tab ((s, MGuarded (GFrom (PCon c vs) w') m):sms) | applySubst s w'==w
>                               = gather w (insert s c vs m tab) sms
>   gather w tab sms            = makeCase w tab : groupMatches sms


> -- Definitions of CaseTable data structures:
> type CaseTable = [(Inst, [CaseAlt])]
> type CaseAlt   = ([Id], Subst, Match)

> -- Insert an alternative into case table, adding the new alternative
> -- after any existing alternative for the same constructor:
> insert             :: Subst -> Inst -> [Id] -> Match -> CaseTable -> CaseTable
> insert s c vs m tab = ins tab
>  where alt                  = [(vs, s, m)]

>        ins                 :: CaseTable -> CaseTable
>        ins []                 = [(c, alt)]
>        ins ((d,alts):tab)
>          | cname c == cname d = (d, alts ++ alt) : tab
>          | otherwise          = (d, alts) : ins tab

>        cname (Inst i _ _) = i


> -- Construct a match expression from a case table:
> makeCase      :: Id -> CaseTable -> Match
> makeCase w tab = foldr1 MElse (map toMatch tab)
>  where toMatch (c, alts) = foldr1 MElse [MGuarded (GFrom (PCon c is) w) (pmcMatches [(s, m)]) | (is, s, m) <- alts]
