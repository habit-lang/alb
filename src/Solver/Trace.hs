module Solver.Trace where

import Control.Monad
import Data.IORef
import Data.List (intercalate)
import qualified Data.IntSet as Set
import qualified Debug.Trace as Trace
import System.Exit
import System.IO
import System.IO.Unsafe

{-# NOINLINE trace #-}
{-# NOINLINE traceInput #-}
{-# NOINLINE doTrace #-}
{-# NOINLINE doTraceInput #-}

trace, traceInput     :: String -> a -> a
doTrace, doTraceInput :: IORef Bool

doTrace      = unsafePerformIO (newIORef False)
doTraceInput = unsafePerformIO (newIORef False)

trace_ bref s x = unsafePerformIO (do b <- readIORef bref
                                      when b (Trace.traceIO s)
                                      return x)

trace      = trace_ doTrace
traceInput = trace_ doTraceInput

traceIf          :: Bool -> String -> a -> a
traceIf True s x  = trace s x
traceIf False _ x = x

{-# NOINLINE check #-}
{-# NOINLINE doCheck #-}
{-# NOINLINE checkSolverTreeDepth #-}
{-# NOINLINE checkSimplificationIterations #-}

doCheck = unsafePerformIO (newIORef True)
checkSolverTreeDepth = unsafePerformIO (newIORef 200)
checkSimplificationIterations = unsafePerformIO (newIORef 20)
checkTrailLength = unsafePerformIO (newIORef (1000 :: Int))

check :: IORef t -> (t -> Bool) -> String -> a -> a
check ref pred failMsg success =
    unsafePerformIO (do b <- readIORef doCheck
                        if b
                        then do v <- readIORef ref
                                if pred v then fail else return success
                        else return success)
    where fail = do hPutStr stderr ("=== SOLVER CHECK FAILED ===\n" ++ failMsg)
                    hFlush stderr
                    exitFailure

showSet :: Set.IntSet -> String
showSet s = "{" ++ intercalate ", " (map show (Set.toList s)) ++ "}"
