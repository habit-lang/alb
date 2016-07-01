{-# LANGUAGE FlexibleContexts, Rank2Types #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Fidget.RenameTypes (renameProgramCtors, renameProgramTypes) where

-- This module uniquely renames types and constructors.
-- As a result, all type applications become nullary.

-- There are two passes in this module: renameProgramCtors and renameProgramTypes.
-- The first should be done immediately before the latter.

import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map

import Common
import Syntax.Common
import Syntax.LambdaCase
import Typechecker.LambdaCasePrims
import Typechecker.LambdaCaseTyping
import Printer.LambdaCase
import Fidget.Mangle (mangleId)

--------------------------------------------------------------------------------

-- Top-down version of everywhereM
everywhereM' :: Monad m => GenericM m -> GenericM m
everywhereM' f x = f x >>= gmapM (everywhereM' f)

type C a = ReaderT CtorEnv Base a
type CtorEnv = Map.Map (Id, [Type]) Id

renameProgramCtors p = liftBase $ runReaderT (do
  env <- build_ctor_env (topDecls p)
  local (const env) (renameCtors p)) Map.empty

build_ctor_env :: [TopDecl] -> C CtorEnv
build_ctor_env tds = liftM Map.fromList (concatMapM build tds) where
  build :: TopDecl -> C [((Id, [Type]), Id)]
  build (Datatype _ [] _) = return []
  build (Datatype tcon ts ctors) =
    mapM (\(id, args) -> fresh id >>= \id' -> return ((id, ts), id')) ctors
  build (Bitdatatype tcon _ dcons) = return []
  build (Struct _ _ _) = return []
  build (Area _ _ _ _ _ _) = return []

renameCtorsTopDecl (Datatype tcon ts ctors) = do
    ctors' <- mapM f ctors
    return (Datatype tcon ts ctors')
    where f (ctor, args) = do
            ctor' <- asks (Map.findWithDefault ctor (ctor, ts))
            return (ctor', args)
renameCtorsTopDecl e = return e

renameCtorsExpr (ECon ctor ts t) = do
    ctor' <- asks (Map.findWithDefault ctor (ctor, ts))
    return (ECon ctor' [] t)
renameCtorsExpr e = return e

renameCtorsAlt (Alt ctor ts vars body) = do
  ctor' <- asks (Map.findWithDefault ctor (ctor, ts))
  return (Alt ctor' [] vars body)

renameCtors :: Program -> C Program
renameCtors = everywhereM' (mkM renameCtorsTopDecl `extM` renameCtorsExpr `extM` renameCtorsAlt)

--------------------------------------------------------------------------------

type T a = ReaderT TypEnv Base a
type TypEnv = Map.Map Type Type

renameProgramTypes p = liftBase $ runReaderT (do
  env <- build_type_env (topDecls p)
  local (const env) (renameTypes p)) Map.empty

intT = bits (natT word_size)

build_type_env :: [TopDecl] -> T TypEnv
build_type_env tds = liftM Map.fromList (concatMapM build tds) where
  build :: TopDecl -> T [(Type, Type)]
  build (Datatype _ [] _) = return []
  build (Datatype tcon ts ctors) = do
    -- In order to help debugging, we try to come up with semi-sensible names
    tcon' <- fresh $ fromString $
             foldl (\x y -> x ++ "_" ++ y) (fromId $ freshPrefix tcon 0) $
             map (fromId . mangleId . fromString . filter (/= ' ') .
                  show . ppr . everywhere (mkT (flip freshPrefix 0))) $
             ts
    return [(type_from_tcon tcon ts, (TyCon (Kinded tcon' KStar)))]
  build (Bitdatatype tcon _ dcons) = do
    tcon' <- fresh tcon
    return [(type_from_tcon tcon [], intT)]
  build (Struct _ _ _) = return []
  build (Area _ _ _ _ _ _) = return []

renameTypesType :: Type -> T Type
renameTypesType t = do
  t' <- asks (Map.lookup t)
  case t' of
    Just t' -> return t'
    Nothing -> return t

renameTypesTopDecl (Datatype tcon ts ctors) = do
  TyCon (Kinded tcon' KStar) <- asks (Map.findWithDefault
                                           (TyCon (Kinded tcon KStar))
                                           (type_from_tcon tcon ts))
  return (Datatype tcon' [] ctors)
renameTypesTopDecl e = return e

renameTypes :: Program -> T Program
renameTypes = everywhereM' (mkM renameTypesType `extM` renameTypesTopDecl)
