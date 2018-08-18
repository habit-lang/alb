> module Syntax.LambdaCase.SCC(sccDecls) where

The code in this module performs a dependency analysis on a list of lambda
case declarations to organize the definitions into binding groups (Mutual
or Nonrec).  The implementation uses a single traversal of the abstract
syntax tree, computing free variable information on the fly and running a
strongly connected components algorithm on every Mutual group in the input
program.

> import Data.Graph(stronglyConnComp, SCC(..))
> import Data.List(union, intersect, (\\), delete)
> import Syntax.Common
> import Syntax.LambdaCase

Transform the input "expression" e by performing dependency analysis on
every Mutual group that it contains, returning the transformed version
of e as well as the set of free variables in e.

> class FvsSCC e where
>   fvsSCC :: e -> (e, [Id])

> instance FvsSCC Expr where
>   fvsSCC e@(EVar i t)
>     = (e, [i])

>   fvsSCC (EBitCon i es)
>     = (EBitCon i es', concat vss)
>       where (es', vss) = unzip (map sccField es)
>             sccField (f, e) = ((f, e'), vs)
>                 where (e', vs) = fvsSCC e

>   fvsSCC (EStructInit k fs)
>     = (EStructInit k fs', concat vss)
>       where (fs', vss) = unzip (map sccField fs)
>             sccField (f, e) = ((f, e'), vs)
>                 where (e', vs) = fvsSCC e

>   fvsSCC (ELam i t e)
>     = (ELam i t e', delete i efvs)
>       where (e', efvs) = fvsSCC e

>   fvsSCC (ELet (Decls ds) e)
>     = (ELet (Decls ds') e', fvs)
>       where (ds', e', fvs) = fvsSCCs ds e

>   fvsSCC (ECase e alts)
>     = (ECase e' alts', foldl union efvs afvs)
>       where (e', efvs)    = fvsSCC e
>             (alts', afvs) = unzip (map fvsSCC alts)

>   fvsSCC (EApp f x)
>     = (EApp f' x', ffvs `union` xfvs)
>       where (f', ffvs) = fvsSCC f
>             (x', xfvs) = fvsSCC x

>   fvsSCC (EBitSelect e f)
>     = (EBitSelect e' f, vs)
>       where (e', vs) = fvsSCC e

>   fvsSCC (EBitUpdate e1 f e2)
>     = (EBitUpdate e1' f e2', vs ++ ws)
>       where (e1', vs) = fvsSCC e1
>             (e2', ws) = fvsSCC e2

>   fvsSCC (EFatbar l r)
>     = (EFatbar l' r', lfvs `union` rfvs)
>       where (l', lfvs) = fvsSCC l
>             (r', rfvs) = fvsSCC r

>   fvsSCC (EBind i t e e1)
>     = (EBind i t e' e1', efvs `union` delete i e1fvs)
>        where (e',  efvs)  = fvsSCC e
>              (e1', e1fvs) = fvsSCC e1

>   fvsSCC (EReturn e)
>     = (EReturn e', vs)
>       where (e', vs) = fvsSCC e

>   fvsSCC e = (e, []) -- covers EPrim, EBits, ENat, ECon

> instance FvsSCC Alt where
>   fvsSCC (Alt c ts is e) = (Alt c ts is e', efvs \\ is)
>    where (e', efvs) = fvsSCC e

> instance FvsSCC Defn where
>   fvsSCC (Defn i t (Left impl)) = (Defn i t (Left impl), [])
>   fvsSCC (Defn i t (Right e)) = (Defn i t (Right e'), efvs)
>    where (e', efvs) = fvsSCC e

A variant of fvsSCC that is used for processing ELet expressions where a
list of declarations scopes over a given expression.

> fvsSCCs :: [Decl] -> Expr -> ([Decl], Expr, [Id])
> fvsSCCs [] e
>   = ([], e', efvs)
>     where (e', efvs) = fvsSCC e

> fvsSCCs (Nonrec d : ds) e
>   = (Nonrec d':ds', e', dfvs `union` delete (defnId d) fvs)
>     where (d', dfvs)     = fvsSCC d
>           (ds', e', fvs) = fvsSCCs ds e

> fvsSCCs (Mutual ms:ds) e
>   = (cs'++ds', e', (msfvs `union` fvs) \\ bound)
>     where (cs', bound, msfvs) = scc ms
>           (ds', e', fvs)      = fvsSCCs ds e

Break a group of definitions into separate binding groups.  We use the
computed free variable information for each definition to build up a
description of the dependency graph for this set of definition in the
format that is required by Data.Graph.stronglyConnComp:

> scc      :: [Defn] -> ([Decl], [Id], [Id])
> scc defns = (comps, bound, foldl union [] dfvss \\ bound)
>  where (ds', dfvss)        = unzip (map fvsSCC defns)
>        bound               = map defnId defns
>        from (CyclicSCC ds) = Mutual ds
>        from (AcyclicSCC d) = Nonrec d
>        ix i                = length (takeWhile (i/=) bound)
>        comps               = map from (stronglyConnComp nodes)
>        nodes               = zip3 ds' [0..]
>                            $ map (map ix . intersect bound) dfvss

> defnId             :: Defn -> Id
> defnId (Defn i _ _) = i

> sccDecls :: Decls -> Decls
> sccDecls (Decls decls) = Decls (concatMap sccDecl decls)
>  where sccDecl (Nonrec d)  = [Nonrec (fst (fvsSCC d))]
>        sccDecl (Mutual ds) = ds'
>                              where (ds',_,_) = scc ds

> -- dump nodes
> --   = unlines [ show (i, ix, links) | (Defn i t e, ix, links) <- nodes ]
