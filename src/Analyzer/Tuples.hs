{-# LANGUAGE Rank2Types, FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Analyzer.Tuples (eliminateTuplesProgram, patternTuplesProgram, generateTuples, TupleState) where

-- This module replaces infix forms with equivalent data types and
-- constructors.  It operates in three phases:
--  * eliminateTuplesProgram: eliminates tuple expression from the program
--  * patternTuplesProgram: eliminates tuple patterns from the program
--  * generateTuples: generate datatype declarations the ruple types

-- eliminateTuplesProgram runs before the rest of desugaring so there
-- is one fewer type of expression that desugaring needs to deal with.
-- However, some parts of desugaring *add* tuple patterns.  Thus, we
-- run patternTuplesProgram *after* desugaring.  Finally, generate
-- tuples creates the appropriate data-types.

-- In order to coordinate between these phases, we maintain a bit of
-- state that record what size of tuples should be generated by
-- generateTuples.  Also since this function is run on a per-file
-- basis instead of a per-program basis, we maintain some state to
-- avoid generating tuple types that were already generated for other
-- files.

import Control.Monad.Writer
import Control.Monad.State
import Data.Generics
import qualified Data.IntSet as Set
import GHC.Base (ap)

import Common
import Syntax.Common
import qualified Syntax.Surface as S
import qualified Syntax.IMPEG as I

-- We have to be careful to avoid generating tuples that we've
-- already generated for other files.
type TupleState = (Set.IntSet{-already generated-}, Set.IntSet{-to be generated-})
type M a = WriterT Set.IntSet Base a

everywhereButM' :: (Monad m) => GenericQ Bool -> GenericM m -> GenericM m
everywhereButM' q f x
  | q x = return x
  | otherwise = gmapM (everywhereButM' q f) =<< f x

needTuple :: Int -> M Id
needTuple n = do tell (Set.singleton n)
                 return (tupleName n)

tupleName :: Int -> Id
tupleName n = fromString ("$Tuple" ++ show n)

--------------------------------------------------------------------------------
-- Eliminating tuples from a program
--------------------------------------------------------------------------------

eliminateTuplesProgram :: Has s TupleState => Pass s S.Program S.Program
eliminateTuplesProgram = up body
    where body :: Pass TupleState S.Program S.Program
          body p = do (old_tuples, new_tuples) <- get
                      (p', tuples') <- liftBase $ runWriterT (elimTuples p)
                      put (old_tuples, Set.union new_tuples tuples')
                      return p'

rebuildTuple con app args = do
  n' <- needTuple (length args)
  return (foldl app' (con n') args)
    where app' t t' = app (introduced t) t'

elimTuplesType (S.TyTupleCon n) = return S.TyCon `ap` needTuple n
elimTuplesType (S.TyTuple ts) = rebuildTuple S.TyCon S.TyApp ts
elimTuplesType e = return e

elimTuplesExpr (S.ETupleCon n) = return S.ECon `ap` needTuple n
elimTuplesExpr (S.ETuple es) = rebuildTuple S.ECon S.EApp es
elimTuplesExpr e = return e

elimTuplesPattern (S.PTupleCon n) = return S.PCon `ap` needTuple n
elimTuplesPattern (S.PTuple ps) = rebuildTuple S.PCon S.PApp ps
elimTuplesPattern e = return e

elimTuples :: S.Program -> M S.Program
elimTuples = everywhereButM'
               (\t -> typeOf t `elem` [typeOf (undefined :: SourcePos),
                                       typeOf (undefined :: Flag),
                                       typeOf (undefined :: Id),
                                       typeOf (undefined :: S.Fixities),
                                       typeOf (undefined :: Kind),
                                       typeOf (undefined :: Literal)])
               (mkM elimTuplesType
                `extM` elimTuplesExpr
                `extM` elimTuplesPattern)

--------------------------------------------------------------------------------
-- Determining what tuples need to be defined to handle pattern bindings
--------------------------------------------------------------------------------

type P = I.PredFN
type Tyid = Id
type Typaram = Either KId Id

patternTuplesProgram :: Has s TupleState => Pass s (I.Program P Tyid Typaram) (I.Program P Tyid Typaram)
patternTuplesProgram = up body
    where body :: Pass TupleState (I.Program P Tyid Typaram) (I.Program P Tyid Typaram)
          body p = do (old_tuples, new_tuples) <- get
                      (p', tuples') <- liftBase $ runWriterT (patternTuples p)
                      put (old_tuples, Set.union new_tuples tuples')
                      return p'

patternTuplesTypingGroup :: I.TypingGroup P Tyid -> M (I.TypingGroup P Tyid)
patternTuplesTypingGroup e@(I.Pattern { I.pattern = p }) =
  needTuple (length (bound p)) >> return e
patternTuplesTypingGroup e = return e

patternTuples :: I.Program P Tyid Typaram -> M (I.Program P Tyid Typaram)
patternTuples = everywhereButM'
                (\t -> typeOf t `elem` [typeOf (undefined :: SourcePos),
                                        typeOf (undefined :: Flag),
                                        typeOf (undefined :: Id),
                                        typeOf (undefined :: Kind),
                                        typeOf (undefined :: Literal)])
                (mkM patternTuplesTypingGroup)

--------------------------------------------------------------------------------
-- Add the tuple definitions that are required
--------------------------------------------------------------------------------

generateTuples :: Has s TupleState =>
                  Pass s (I.Program I.PredFN Id (Either KId Id)) (I.Program I.PredFN Id (Either KId Id))
generateTuples = up body
    where body :: Pass TupleState (I.Program P Tyid Typaram) (I.Program P Tyid Typaram)
          body p = do (old_tuples, new_tuples) <- get
                      put (Set.union old_tuples new_tuples, Set.empty)
                      let tuples = Set.difference new_tuples old_tuples
                          (ts, fs) = unzip $ map generateTuple $ Set.toList tuples
                      return $ p { I.decls = I.Decls (concat fs) `I.appendDecls` I.decls p, I.topDecls = ts ++ I.topDecls p }

generateTuple :: Int -> (Located (I.TopDecl I.PredFN Id (Either KId Id)),
                         [I.TypingGroup I.PredFN Id])
generateTuple n = (introduced $ I.Datatype (tupleName n)
                                  [introduced (Left (Kinded (fromString ("t" ++ show x)) KStar)) | x <- is]
                                  []
                                  [I.Ctor (introduced (tupleName n)) [] []
                                        [introduced (I.TyVar (fromString ("t" ++ show x))) | x <- is]]
                                  ["Eq", "Ord", "Bounded"],
                   [buildTupleSelector m | m <- [0..n-1]])
    where is = [0..n - 1]
          buildTupleSelector m = I.Explicit (selectorName, ["$x"], body) tys
              where selectorName = fromString ("$t" ++ show n ++ '_' : show m)
                    body = I.MGuarded
                           (I.GFrom (introduced (I.PCon (tupleName n) [fromString ("$x" ++ show m) | m <- is]))
                                 (introduced (I.EVar "$x")))
                           (I.MCommit (introduced (I.EVar (fromString ("$x" ++ show m)))))
                    tys = I.ForallK []
                            (I.Forall [fromString ('t' : show i) | i <- [0..n-1]]
                              ([] I.:=> introduced (foldl tyapp
                                                          (I.TyCon (tupleName n))
                                                          [I.TyGen m | m <- is] `to` I.TyGen m)))
                    tyapp t t' = I.TyApp (introduced t) (introduced t')
                    t `to` t'  = tyapp (tyapp (I.TyCon "->") t) t'
