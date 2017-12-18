module Solver.RunTests where

import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.Process

data Test = T [String] String | X [String] String deriving (Read, Show)

main = do hSetBuffering stdout NoBuffering
          args <- getArgs
          when (args == ["setup"]) (setup >> exitSuccess)
          when (args == ["perf"]) (perf >> exitSuccess)
          tests <- (map read . lines) `fmap` readFile "./tests/solver/catalog"
          results <- mapM check tests
          case catMaybes results of
            [] -> putStrLn "ok"
            ts -> putStrLn ("fail:\n" ++ unlines (map show ts))

check (T args resultsFile) =
    do putStr resultsFile
       (_, Just stdout, _, _) <- createProcess (proc "./ilab" args) { std_out = CreatePipe }
       actual <- hGetContents stdout
       intended <- readFile resultsFile
       if actual == intended
          then do putStr clear
                  putStr "."
                  return Nothing
          else do putStr clear
                  putStr "X"
                  writeFile ("./actual-" ++ (takeFileName resultsFile)) actual
                  return (Just (T args resultsFile))
    where clear = replicate (length resultsFile) (chr 8) ++ replicate (length resultsFile) ' ' ++ replicate (length resultsFile) (chr 8)
check (X _ _) =
    do putStr "O"
       return Nothing

setup = do tests <- (map read . lines) `fmap` readFile "./tests/solver/catalog"
           mapM_ setup' tests
           putStrLn ""
    where setup' (X _ _) =
              putStr "O"
          setup' (T args resultsFile) =
              do putStr resultsFile
                 (_, Just stdout, _, _) <- createProcess (proc "./ilab" args) { std_out = CreatePipe }
                 actual <- hGetContents stdout
                 writeFile resultsFile actual
                 putStr clear
                 putStr "."
              where clear = replicate (length resultsFile) (chr 8) ++ replicate (length resultsFile) ' ' ++ replicate (length resultsFile) (chr 8)

perf = do tests <- (map read . lines) `fmap` readFile "./tests/solver/catalog"
          let nonProofs = [args | T args _ <- tests, all ("-p" /=) args]
              args      = ["+RTS", "-p", "-RTS"] ++ intercalate ["-r"] nonProofs
          createProcess (proc "./ilabp" args)
