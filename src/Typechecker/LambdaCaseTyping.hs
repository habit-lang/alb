{-# LANGUAGE OverloadedStrings #-}
module Typechecker.LambdaCaseTyping where

import Syntax.Common
import Syntax.LambdaCase
import Typechecker.LambdaCasePrims
import Printer.LambdaCase
import Fidget.Env

-- Split off fun type args
uncurry_type :: Type -> ([Type],Type)
uncurry_type (TyApp (TyApp (TyCon (Kinded "->" _)) t1) t2) =  (t1:ts',r)
   where (ts',r) = uncurry_type t2
uncurry_type t = ([],t)

-- Build fully-saturated type from type constructor name and parameter instances
type_from_tcon :: Id -> [Type] -> Type
type_from_tcon d ts =
    tapplyn (TyCon (Kinded d (foldr ( \_ k -> KStar `KFun` k) KStar ts))) ts

-- Build environment of typing info for data constructors.
-- Maps (dcon id,instantiating types) to full dcon type
build_dcon_tcon_env :: [TopDecl] -> Env (Id,[Type]) Type
build_dcon_tcon_env tds = foldr build empty_env tds
  where build :: TopDecl -> Env (Id,[Type]) Type -> Env (Id,[Type]) Type
        build (Datatype tcon ts cs) env =
               foldr (\ (dcon,argts) env ->
                            extend_env env (dcon,ts)
                                       (foldr fun (type_from_tcon tcon ts) argts)) env cs
        build (Bitdatatype tcon _ cs) env =
               foldr (\ (dcon,_) env ->
                            extend_env env (dcon,[])
                                           (fun (bitdatacase tcon dcon) (type_from_tcon tcon []))) env cs
        build _ env = env -- for now

-- Type reconstruction
type_of :: Expr -> Type
type_of (EVar x t) = t
type_of (EBits n s) = bits (TyLit (fromIntegral s)) -- not sure how this will translate
type_of (ENat n) = natT n
type_of (ECon c ts t) = t
type_of (ELam _ t e) = t `fun` type_of e
type_of (ELet _ e) = type_of e
type_of (ECase _ (Alt _ _ _ e:_)) = type_of e
type_of (EApp e1 e2) =
  case type_of e1 of
    TyApp (TyApp (TyCon (Kinded "->" _)) t1) t2 -> t2
    _ -> error $ "impossible type_of " ++ show (ppr e1) ++ ":" ++ show (ppr (type_of e1))
type_of (EFatbar e1 _) = type_of e1
type_of (EBind _ _ _ e) = type_of e
