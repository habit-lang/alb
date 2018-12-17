module Normalizer.Eta where

import Syntax.Specialized

import Data.Generics


etaExpandDefn :: Defn -> Defn
etaExpandDefn d@(Defn _ _ (Left _)) = d
etaExpandDefn d@(Defn id (Forall [] [] ty) (Right (Gen tvars evars e))) =
    case e of
      ELam{} -> d
      _ -> case ty of
             TyApp (TyApp (TyCon (Kinded "->" _)) dom) _ ->
                 Defn id (Forall [] [] ty) (Right (Gen tvars evars (ELam "$a" dom (EApp e (ELamVar "$a")))))
             _ -> d

etaExpand  :: Specialized -> Specialized
etaExpand = everywhere (mkT etaExpandDefn)
