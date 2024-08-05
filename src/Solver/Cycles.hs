{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Solver.Cycles (cyclic) where

import Control.Monad.State
import Data.Maybe
import Solver.PP
import Solver.Syntax
import Solver.Trace

import GHC.Base (liftM2)

newtype M t = M { runM :: State [(Id, [Id])] t }
    deriving (Functor, Applicative, Monad, MonadState [(Id, [Id])])

cyclic :: [Proof] -> Bool
cyclic ps = evalState (runM (anyM cyclic' ps)) []

cyclic' (PAx v _ _ _ ps) =
    do assumes v vs
       as <- concatMapM assumedBy vs
       b <- anyM cyclic' ps
       traceIf (v `elem` vs || v `elem` as) ("Cyclic proof for: " ++ ppx v) $
           return (v `elem` vs || v `elem` as || b)
    where vs = concatMap assumptionsIn ps
cyclic' (PCases v cs) =
    do assumes v vs
       as <- concatMapM assumedBy vs
       b <- anyM cyclic' ps
       traceIf (v `elem` vs || v `elem` as) ("Cyclic proof for: " ++ ppx v) $
           return (v `elem` vs || v `elem` as || b)
    where ps = [pr | (_, _, pr) <- cs]
          vs = concatMap assumptionsIn ps
cyclic' (PComputedCases {}) = return False
cyclic' (PAssump v v')
    | v == v' = return False
    | otherwise = do assumes v [v']
                     vs <- assumedBy v'
                     traceIf (v `elem` vs) ("Cyclic proof for: " ++ ppx v) $
                         return (v `elem` vs)
cyclic' (PRequired v _ ps) =
    do assumes v vs
       as <- concatMapM assumedBy vs
       b <- anyM cyclic' ps
       traceIf (v `elem` vs || v `elem` as) ("Cyclic proof for: " ++ ppx v) $
           return (v `elem` vs || v `elem` as || b)
    where vs = concatMap assumptionsIn ps
cyclic' (PClause v _ _ ps) =
    do assumes v vs
       as <- concatMapM assumedBy vs
       b <- anyM cyclic' ps
       traceIf (v `elem` vs || v `elem` as) ("Cyclic proof for: " ++ ppx v) $
           return (v `elem` vs || v `elem` as || b)
    where vs = concatMap assumptionsIn ps
cyclic' (PFrom v p p') = liftM2 (||) (cyclic' p) (cyclic' p')
cyclic' (PSkip _ (_, p)) = cyclic' p
cyclic' PInapplicable = return False
cyclic' PExFalso = return False

anyM :: (Functor m, Monad m) => (t -> m Bool) -> [t] -> m Bool
anyM f xs = or `fmap` mapM f xs

assumes :: Id -> [Id] -> M ()
assumes id ids = modify (\ps -> (id, ids) : ps)

assumedBy :: Id -> M [Id]
assumedBy id = gets (fromMaybe [] . lookup id)
