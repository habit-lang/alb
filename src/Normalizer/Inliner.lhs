> {-# LANGUAGE FlexibleInstances, PatternGuards #-}
> module Normalizer.Inliner(inlineProgram) where

The code in this module performs a simple inlining pass on LambdaCase
declarations lists, eliminating trivial bindings of the form v = e where e is
either an EPrim or an EVar.  It also attempts to rename bindings with names
that might not be linker friendly.

Come to think of it, this code could easily be modified to propagate type
annotations to EVar nodes if we weren't going to rely on full type checking.

> import Data.Char (ord, isAlphaNum, isAlpha)
> import Data.Maybe (fromMaybe, fromJust)
> import Syntax.Common
> import Syntax.LambdaCase

A simple environment mapping

> type Env        = [(Id, Expr)]

> unbind         :: Id -> Env -> Env
> unbind i env    = [ p | p@(j,_) <- env, i/=j ]

> unbinds        :: [Id] -> Env -> Env
> unbinds is env  = [ p | p@(j,_) <- env, j `notElem` is ]

> extend, recextend  :: Id -> Expr -> Env -> Env
> extend i e env      = (i, e) : env
> recextend i e env   = (i, e) : map app env
>  where app (i', EVar j t) | j==i  = (i', e)
>        app p                      = p

Transform the input "expression" e by performing dependency analysis on every
Mutual group that it contains, returning the transformed version of e as well
as the set of free variables in e.

> class Inliner e where
>   inline :: Env -> e -> e

> instance Inliner (Either (String, [Type]) Expr) where
>   inline env (Left impl) = Left impl
>   inline env (Right e) = Right (inline env e)

> instance Inliner Expr where
>   inline env e@(EVar i t)             = fromMaybe e (lookup i env)
>   inline env (EBitCon i fields)       = EBitCon i [(f, inline env e) | (f, e) <- fields]
>   inline env (EStructInit k fields)   = EStructInit k [(f, inline env e) | (f, e) <- fields]
>   inline env (ELam i t e)             = ELam i t (inline (unbind i env) e)
>   inline env (ELet (Decls ds) e)      = let (env', ds') = inlineGroups [] env ds -- NOTE: refusing to preserve let-bound values
>                                         in case ds' of
>                                              [] -> inline env' e
>                                              _  -> ELet (Decls ds') (inline env' e)
>   inline env (ECase e alts)           = ECase (inline env e) (map (inline env) alts)
>   inline env (EApp f x)               = EApp (inline env f) (inline env x)
>   inline env (EBitSelect e f)         = EBitSelect (inline env e) f
>   inline env (EBitUpdate e f e')      = EBitUpdate (inline env e) f (inline env e')
>   inline env (EFatbar l r)            = EFatbar (inline env l) (inline env r)
>   inline env (EBind i t e e1)         = EBind i t (inline env e) (inline (unbind i env) e1)
>   inline env (EReturn e)              = EReturn (inline env e)
>   inline env e                        = e -- covers EPrim, EBits, ENat, ECon

> instance Inliner Alt where
>   inline env (Alt c ts is e) = Alt c ts is (inline (unbinds is env) e)

> instance Inliner Defn where
>   inline env (Defn i t (Left impl))  = Defn i t (Left impl)
>   inline env (Defn i t (Right e)) = Defn i t (Right (inline env e))

> instance Inliner TopDecl where
>   inline env (Area name v init ty size align) = Area name v (inline env init) ty size align
>   inline env d                                = d -- covers Datatype, Bitdatatype, Struct

> inlineable        :: Expr -> Bool
> inlineable EVar{}  = True
> inlineable EBits{} = True
> inlineable ENat{}  = True
> inlineable ECon{}  = True
> inlineable EBitCon{} = True
> inlineable EBitSelect{} = True
> inlineable EBitUpdate{} = True
> inlineable _       = False

> inlineGroups         :: [Id] -> Env -> [Decl] -> (Env, [Decl])
> inlineGroups _ env [] = (env, [])
> inlineGroups preserved env (Nonrec (Defn i t e) : defns)
>       | Right e' <- e,
>         i `notElem` preserved && inlineable e' = inlineGroups preserved (extend i (inline env e') env) defns
>       | otherwise                              = let (env', defns') = inlineGroups preserved env defns
>                                                 in  (env', Nonrec (Defn i t (inline env e)) : defns')
> inlineGroups preserved env (Mutual ds : defns)
>   = splitDefns [] [] ds
>     where splitDefns          :: Env -> [Defn] -> [Defn] -> (Env, [Decl])
>           splitDefns dsenv ds (d@(Defn i t e):rest)
>               | Right e' <- e,
>                 i `notElem` preserved && inlineable e' = splitDefns (recextend i (inline dsenv e') dsenv) ds rest
>               | otherwise                              = splitDefns dsenv (d:ds) rest
>           splitDefns dsenv ds []
>             = case ds of
>                 [] -> error "cyclic substitution"
>                 _  -> let env'            = dsenv ++ env
>                           (env'', defns') = inlineGroups preserved env' defns
>                       in (env'', Mutual (map (inline env') ds) : defns')

> inlineDecls :: [Id] -> Env -> Decls -> (Env, Decls)
> inlineDecls preserved env (Decls ds)
>     = (env', Decls ds')
>     where (env', ds') = inlineGroups preserved env ds

> inlineProgram :: [(Id, Bool)] -> Program -> Program
> inlineProgram preserved (Program decls topDecls)
>     = Program decls' topDecls'
>     where (env, decls')   = inlineDecls (map fst preserved) [] decls
>           topDecls'       = map (inline env) topDecls
