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
> import Syntax.XMPEG
> import Syntax.Specialized

A simple environment mapping

> type Env        = [(Id, (Scheme Type, Expr))]

> unbind         :: Id -> Env -> Env
> unbind i env    = [ p | p@(j,_) <- env, i/=j ]

> unbinds        :: [Id] -> Env -> Env
> unbinds is env  = [ p | p@(j,_) <- env, j `notElem` is ]

> extend, recextend  :: Id -> Scheme Type -> Expr -> Env -> Env
> extend i t e env      = (i, (t, e)) : env
> recextend i t e env   = (i, (t, e)) : map app env
>  where app (i', (t, ELamVar j)) | j==i  = (i', (t, e))
>        app p                            = p

Transform the input "expression" e by performing dependency analysis on every
Mutual group that it contains, returning the transformed version of e as well
as the set of free variables in e.

> class Inliner e where
>   inline :: Env -> e -> e

> instance Inliner (Either (String, [Type]) Expr) where
>   inline env (Left impl) = Left impl
>   inline env (Right e) = Right (inline env e)

> instance Inliner Expr where
>   inline env e@(ELamVar i)            = fromMaybe e (snd `fmap` lookup i env)
>   inline _   (ELetVar _)              = error "Inliner.lhs:46"
>   inline env (EBitCon i fields)       = EBitCon i [(f, inline env e) | (f, e) <- fields]
>   inline env (EStructInit k fields)   = EStructInit k [(f, inline env e) | (f, e) <- fields]
>   inline env (ELam i t e)             = ELam i t (inline (unbind i env) e)
>   inline env (ELet ds e)              = let (env', ds') = inlineDecls [] env ds -- NOTE: refusing to preserve let-bound values
>                                         in case ds' of
>                                              Decls [] -> inline env' e
>                                              _  -> ELet ds' (inline env' e)
>   inline env (EMatch m)               = EMatch (inline env m)
>   inline env (EApp f x)               = EApp (inline env f) (inline env x)
>   inline env (EBitSelect e f)         = EBitSelect (inline env e) f
>   inline env (EBitUpdate e f e')      = EBitUpdate (inline env e) f (inline env e')
>   inline env (EBind ta tb tm me i e e1) = EBind ta tb tm me i (inline env e) (inline (unbind i env) e1)
>   inline env (EReturn e)              = EReturn (inline env e)
>   inline env e                        = e -- covers EPrim, EBits, ENat, ECon

> instance Inliner Match where
>   inline _ MFail = MFail
>   inline env (MCommit e) = MCommit (inline env e)
>   inline env (MElse m1 m2) = MElse (inline env m1) (inline env m2)
>   inline env (MGuarded (GFrom PWild _) m) = inline env m
>   inline env (MGuarded (GFrom (PVar v t) w) m) = inline (extend v (Forall [] [] t) (ELamVar w) env) m
>   inline env (MGuarded (GFrom p w) m) =
>       case lookup w env of
>         Nothing -> MGuarded (GFrom p w) (inline env m)
>         Just (_, ELamVar v) -> MGuarded (GFrom p v) (inline env m)
>         Just (t, e) -> MGuarded (GLet (Decls [Defn w t (Right (Gen [] [] e))])) (MGuarded (GFrom p w) (inline env m))
>   inline env (MGuarded (GLet ds) m) = let (env', ds') = inlineDecls [] env ds
>                                       in case ds' of
>                                            Decls [] -> inline env' m
>                                            _  -> MGuarded (GLet ds') (inline env' m)
>   inline env (MGuarded _ _) = error "Inliner.lhs:76" -- GSubst, GLetTypes

> instance Inliner Defn where
>   inline env (Defn i t (Left impl))  = Defn i t (Left impl)
>   inline env (Defn i t (Right (Gen [] [] e))) = Defn i t (Right (Gen [] [] (inline env e)))

> inlineable        :: Expr -> Bool
> inlineable ELamVar{}    = True
> inlineable EBits{}      = True
> inlineable ECon{}       = True
> inlineable EBitCon{}    = True
> inlineable EBitSelect{} = True
> inlineable EBitUpdate{} = True
> inlineable _            = False

> inlineGroups         :: [Id] -> Env -> [Defn] -> (Env, [Defn])
> inlineGroups _ env [] = (env, [])
> inlineGroups preserved env ds
>   = splitDefns env [] ds
>     where splitDefns          :: Env -> [Defn] -> [Defn] -> (Env, [Defn])
>           splitDefns dsenv ds (d@(Defn i t e):rest)
>               | Right (Gen [] [] e') <- e,
>                 i `notElem` preserved && inlineable e' = splitDefns (recextend i t (inline dsenv e') dsenv) ds rest
>               | otherwise                              = splitDefns dsenv (d:ds) rest
>           splitDefns dsenv ds []
>             = let env' = dsenv ++ env
>               in (env', (map (inline env') ds))

> inlineDecls :: [Id] -> Env -> Decls -> (Env, Decls)
> inlineDecls preserved env (Decls ds)
>     = (env', Decls ds')
>     where (env', ds') = inlineGroups preserved env ds

> inlineProgram :: [(Id, Bool)] -> Specialized -> Specialized
> inlineProgram exported (Specialized topDecls entries decls)
>     = Specialized topDecls entries' decls'
>     where preserved       = map fst exported
>           (env, decls')   = inlineDecls preserved [] decls
>           entries'        = [(inline env e, b) | (e, b) <- entries]
