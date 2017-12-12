{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, TupleSections, PatternGuards, Rank2Types #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Fidget.SpecialTypes (specialTypes) where

-- This module replaces types that should be treated "special".  For
-- example, 'Unit' and 'Maybe (Ix n)' are represented with 'Funit' and
-- 'Fint' respectively rather than using 'Ftcon'.
--
-- Note that this module detects 'Unit' and 'Maybe (Ix n)' based on
-- the shape of the type declaration rather than on the name of the
-- type.  Thus any type that looks like a 'Unit' or 'Maybe (Ix n)'
-- will get this optimization.

import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.Generics
import Data.Maybe
import qualified Data.Map as Map

import Common
import Fidget.AST
import Fidget.Typing

type M a = ReaderT (Map.Map Tcon Translation) Base a

specialTypes :: Pass () Program Program
specialTypes (Program globals funcs main init types areas structs) =
  liftBase $ runReaderT
             (optimizeTypes (Program globals funcs main init types' areas structs))
             (Map.fromList detectedTypes)
  where (types', detectedTypes) = partitionEithers (map detectTypes types)
        detectTypes :: (Id, [[Ftyp]]) -> Either (Id, [[Ftyp]]) (Tcon, Translation)
        -- NOTE: Do both orders in case the constructors are swapped
        detectTypes (id, [[], [Fix n]]) = Right (id, maybeIx n 0 1)
        detectTypes (id, [[Fix n], []]) = Right (id, maybeIx n 1 0)
        detectTypes (id, [[], [Fnzero]]) = Right (id, maybeNzero 0 1)
        detectTypes (id, [[Fnzero], []]) = Right (id, maybeNzero 1 0)
        --detectTypes (id, [[], [Ref area]]) = Right (id, maybeRef area 0 1)
        --detectTypes (id, [[Ref area], []]) = Right (id, maybeRef area 1 0)
        detectTypes (id, [[]]) = Right (id, unit)
        detectTypes t = Left t

-- How to translate various forms
data Translation = Translation {
  typ :: Base Ftyp,  -- type
  ctor :: Nat {-tag-} -> [Atom] -> Base SimplExpr, -- constructor application
  load :: Id {-var-} -> Nat {-tag-} -> Nat {-index-} -> Base Atom, -- pattern variable reference
  cas :: Atom -> [(Id, Nat, Expr)] -> Maybe (Id, Expr) -> Base Expr -- case
  }

unit = Translation { typ = typ', ctor = ctor', load = load', cas = cas' } where
  typ' = return Funit
  ctor' 0 [] = return $ Satom (Aconst Ounit)
  ctor' _ _ = undefined
  load' var tag 0 = error "Internal error: impossible Fload from Unit type"
  load' _ _ _ = error "Internal error: impossible Fload from Unit type"
  cas' atom [(var, 0, e)] _ = return e
  cas' atom [] (Just (_, def)) = return def
  cas' _ _ _  = error "This should not happen"

maybeIx ix = maybeType (Fix ix) (Fint) (Oixunsigned ix) (Ointconst ix) (flip Eixcase ix)
maybeNzero = maybeType (Fnzero) (Fint) (Onzunsigned) (Ointconst 0) (Enzcase)
-- TODO: we need "Onull" in order to implement this, but once that exists, this code should work
--maybeRef area = maybeType (Fref area) (Fptr area) (Optr) (Onull area) (flip Erefcase area)

maybeType absType repType justOp nothingConst caseOp nothingTag justTag =
  Translation { typ = typ', ctor = ctor', load = load', cas = cas' } where
  typ' = return repType
  ctor' tag [arg] | tag == justTag = return $ Satom (Aunop justOp arg)
  ctor' tag [] | tag == nothingTag = return $ Satom (Aconst nothingConst)
  ctor' _ _ = error "ctor This should not happen"
  load' var tag 0 | tag == justTag = return $ (Avar var absType)
  load' _ _ _ = error "Load error: This should not happen"
  -- Note: clauses may be missing and in any order
  cas' atom alts def = do
    (_, nothingBody) <- getTag nothingTag alts -- hack: assumes argument isn't used
    (justVar, justBody) <- getTag justTag alts
    return $ caseOp atom justVar justBody nothingBody
    where getTag tag ((var, t, e) : _) | t == tag = return (var, e)
          getTag tag (_ : alts) = getTag tag alts
          getTag tag [] = do id' <- fresh (fst (fromJust def)) -- hack: assumes id isn't used
                             return (id', snd (fromJust def))

----------------------------------------
-- Generic traversal code

optimizeTypesFtyp e@(Ftcon t) = do
  p <- asks (Map.lookup t)
  case p of Just p' -> lift $ typ p'; Nothing -> return e
-- hack: This treats records the same as types.
-- This erases the type distinction between the two,
-- but is OK for now because we don't use the type distinction.
optimizeTypesFtyp e@(Frecordt t tag) = do
  p <- asks (Map.lookup t)
  case p of Just p' -> lift $ typ p'; Nothing -> return e
optimizeTypesFtyp e = return e

optimizeTypesSimplExpr e@(Salloc t tag args) = do
  p <- asks (Map.lookup t)
  case p of Just p' -> lift $ ctor p' tag args; Nothing -> return e
optimizeTypesSimplExpr e = return e

optimizeTypesAtom e@(Aload v@(Avar id (Frecordt t tag)) index _) = do
  p <- asks (Map.lookup t)
  case p of Just p' -> lift $ load p' id tag index; Nothing -> return e
optimizeTypesAtom e = return e

optimizeTypesExpr e@(Ecase a alts def) | Ftcon t <- type_of_atom a = do
  p <- asks (Map.lookup t)
  case p of Just p' -> lift $ cas p' a alts def; Nothing -> return e
optimizeTypesExpr e = return e

-- Top-down version of everywhereM
everywhereM' :: Monad m => GenericM m -> GenericM m
everywhereM' f x = f x >>= gmapM (everywhereM' f)

optimizeTypes :: Program -> M Program
optimizeTypes = everywhereM' (mkM optimizeTypesFtyp
                                `extM` optimizeTypesSimplExpr
                                `extM` optimizeTypesAtom
                                `extM` optimizeTypesExpr)
