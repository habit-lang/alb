{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Fidget.Thunkify (thunkifyLC) where

--------------------------------------------------------------------------------
-- This module contains three passes:
--  1. [mk_init] Generate the "initialize" function
--  2. [thunkify] Convert EBind and monadic primitives into explicit force/delay,
--     and coerce the I monad to the M monad.
--  3. [elimThunks] Eliminate force/delay pairs.
--     (Also converts any var of type "Unit" to a constructor call.)
--------------------------------------------------------------------------------

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Foldable (foldlM, foldrM)
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe

import Common
import Syntax.Common
import Syntax.LambdaCase
import Typechecker.LambdaCasePrims (fun, monadI, ref, unit)
import Fidget.LambdaCaseToFidget (known_prims)

data PrimDecl = PrimDecl { primId :: Id, primType :: Type, primExtern :: String, primTypeArgs :: [Type] }
type M a = Base a
type M' a = StateT [PrimDecl]{-prims declared-} (ReaderT (Map.Map Id Id){-renames-} Base) a
type M'' a = WriterT (Map.Map Id Id){-prim renames-} (StateT [PrimDecl] (ReaderT (Map.Map Id Id) Base)) a

mk_init :: Id -> Program -> M Program
mk_init initialize (Program (Decls decls) topDecls) = do
  ret <- fresh "primReturnI"
  body <- foldrM build_one
                 (EApp (EVar ret (unit `fun` monadI unit)) (ECon "Unit" [] unit))
                 topDecls
  when (any isBoundDecl decls || any isBoundArea topDecls) $
       failWithS $ "Can't generate initializer named '" ++ fromId initialize ++
                   "'.  Name already bound."
  -- We put the initializer at the end because the decls are sorted by dependency
  return $ Program (Decls $
    decls ++ [Nonrec (Defn ret (unit `fun` monadI unit) (Left ("primReturnI", [unit]))),
              Nonrec (Defn initialize (monadI unit) (Right body))])
    topDecls
    where build_one (Area x v e t s a) b = do
            name <- fresh "_"
            return $ EBind name unit (EApp e (EVar x (ref t))) b
          build_one _ b = return b
          isBoundDecl (Mutual defns) = any isBoundDefn defns
          isBoundDecl (Nonrec defn) = isBoundDefn defn
          isBoundDefn (Defn id _ _) = id == initialize
          isBoundArea (Area id _ _ _ _ _) = id == initialize
          isBoundArea _ = False

withPrims e@(Decls ds) m = do
  renames <- mapM (\x -> do x' <- fresh x; return (x, x')) $
             concatMap declPrimVars ds
  local (Map.union (Map.fromList renames)) $ m
  where declPrimVars (Nonrec defn) = defnPrimVars defn
        declPrimVars (Mutual defns) = concatMap defnPrimVars defns
        defnPrimVars (Defn x _ (Left _)) = [x]
        defnPrimVars _ = []

-- Freshen the variable name by which we refer to a prim. Otherwise, it will conflict with the extern.
freshenPrims :: Program -> ReaderT (Map.Map Id Id) Base Program
freshenPrims p = rec p where
  rec :: (Data a) => a -> ReaderT (Map.Map Id Id) Base a
  rec = gmapM rec `extM` program `extM` defn `extM` expr
  program :: Program -> ReaderT (Map.Map Id Id) Base Program
  program p = withPrims (decls p) (gmapM rec p)
  defn (Defn id t body) = do id' <- asks (Map.findWithDefault id id)
                             gmapM rec (Defn id' t body)
  expr (EVar id t) = do id' <- asks (Map.findWithDefault id id)
                        gmapM rec (EVar id' t)
  expr e@(ELet d _) = withPrims d (gmapM rec e)
  expr e = gmapM rec e

delay :: Expr -> M Expr
delay e = fresh "_" >>= \x -> return $ ELam x unit e

force :: Expr -> Expr
force e = EApp e (ECon "Unit" [] unit)

delayt :: Type -> Type
delayt t = unit `fun` t

thunkify_type :: (Type -> Type) -> Type -> Type
thunkify_type delay (TyApp (TyCon (Kinded "M" _)) t) = delay (thunkify_type delay t)
thunkify_type delay (TyApp (TyCon (Kinded "I" _)) t) = delay (thunkify_type delay t)
thunkify_type delay (TyApp t1 t2) = TyApp (thunkify_type delayt t1) (thunkify_type delay t2)
thunkify_type delay t = t

thunkify_prim :: Expr -> Type -> M Expr
thunkify_prim e (TyApp (TyCon (Kinded "M" _)) t) = delay =<< thunkify_prim e t
thunkify_prim e (TyApp (TyCon (Kinded "I" _)) t) = delay =<< thunkify_prim e t
thunkify_prim e (TyApp (TyApp (TyCon (Kinded "->" _)) t1) t2) = do
  x' <- fresh "x"
  body <- thunkify_prim (EApp e (EVar x' (thunkify_type delayt t1))) t2
  return (ELam x' t1 body)
thunkify_prim e t = return e

allocPrims :: Decls -> (Decls -> M' a) -> M' a
allocPrims (Decls ds) k = do
  (decls, renames) <- runWriterT (mapM declPrim ds)
  local (Map.union renames) $ k (Decls decls)
  where declPrim :: Decl -> M'' Decl
        declPrim (Nonrec defn) = liftM Nonrec $ defnPrim defn
        declPrim (Mutual defns) = liftM Mutual $ mapM defnPrim defns
        defnPrim :: Defn -> M'' Defn
        defnPrim (Defn x t (Left (p, ts))) = do
          x' <- lift $ fresh x
          x'' <- if p `elem` known_prims
                 then lift $ fresh x -- Known prims need unique names due to different type instantiations
                 else return (fromString p) -- CompCert requires the binder name to match the RHS
          body <- lift $ lift $ lift $ thunkify_prim (EVar x'' (thunkify_type id t)) t
          tell (Map.singleton x x')
          modify (PrimDecl { primId = x'', primType = thunkify_type id t, primExtern = p,
                             primTypeArgs = map (thunkify_type delayt) ts } :)
          return $ Defn x' t (Right body)
        defnPrim x = return x

thunkify :: Program -> M Program
thunkify p = do
  (p', primDecls) <- runReaderT (runStateT (thunkify' p) []) Map.empty
  let Decls funDecls = decls p'
  return (p' { decls = Decls $ map primDecl primDecls ++ funDecls})
  where primDecl :: PrimDecl -> Decl
        primDecl p = Nonrec $ Defn (primId p) (primType p) (Left (primExtern p, primTypeArgs p))

thunkify' :: Program -> M' Program
thunkify' p = rec p where
  rec :: (Data a) => a -> M' a
  rec = gmapM rec `extM` (return . thunkify_type delayt) `extM` expr `extM` program
  program p = allocPrims (decls p) (\decls' -> gmapM rec (p { decls = decls' }))
  expr (EVar id t) = do id' <- asks (Map.findWithDefault id id)
                        gmapM rec (EVar id' t)
  expr (ELet d body) = allocPrims d (\d' -> gmapM rec (ELet d' body))
  expr (EBind x t e1 e2) = do
    t' <- rec t
    e1' <- rec e1
    e2' <- rec e2
    lift $ lift $ delay (ELet (Decls [Nonrec (Defn x t' (Right (force e1')))]) (force e2'))
  expr e = gmapM rec e


elim_thunks (EVar _ t) | t == unit = ECon "Unit" [] unit
elim_thunks (EApp (ELam _ _ e) (ECon "Unit" [] _)) = e
elim_thunks e = e

elimThunks :: Program -> Program
elimThunks = everywhere (mkT elim_thunks)

thunkifyLC :: Id -> Pass () Program Program
thunkifyLC initialize p = liftBase $ do
  return p >>= mk_init initialize >>= (\x -> runReaderT (freshenPrims x) Map.empty)
           >>= thunkify >>= return . elimThunks
