module Solver.REPL where

import Control.Monad
import Data.Char
import Data.IORef
import Data.List
import System.Environment (getArgs)
import System.IO
import Text.Parsec hiding (Ok)

import Solver.Cycles
import Solver.Main hiding (run)
import qualified Solver.Main as S
import Solver.Oracles as O
import Solver.Parser
import Solver.PP
import Solver.Subst
import Solver.Syntax
import Solver.Tactics hiding (remaining)
import Solver.Trace hiding (trace)
import Solver.Validation

import Debug.Trace

main = do args <- getArgs
          let (showProofs, args1)                = checkShowProofs args
              (showNodeCount, args2)             = checkShowNodeCount args1
              (showTrace, showTraceInput, args3) = checkTrace args2
              (checks, args4)                    = checkChecks args3
              (maxDepth, args5)                  = checkNumericArg "-cd" args4
              (maxSimplIters, args6)             = checkNumericArg "-ci" args5
              (maxTrailLength, args7)            = checkNumericArg "-ct" args6
              (after, remaining)                 = checkAfter args7
          writeIORef doTrace showTrace
          writeIORef doTraceInput showTraceInput
          writeIORef doCheck checks
          maybeWriteIORef maxDepth checkSolverTreeDepth
          maybeWriteIORef maxSimplIters checkSimplificationIterations
          maybeWriteIORef maxTrailLength checkTrailLength
          run showProofs showNodeCount [] O.fundeps [] [] remaining >>= after showProofs showNodeCount
    where  checkShowProofs args | "-p" `elem` args = (True, filter ("-p" /=) args)
                                | otherwise        = (False, args)
           checkShowNodeCount args | "-n" `elem` args = (True, filter ("-n" /=) args)
                                   | otherwise        = (False, args)
           checkTrace args | "-t" `elem` args = (True, True, filter ("-t" /=) args)
                           | "-ti" `elem` args = (False, True, filter ("-ti" /=) args)
                           | otherwise        = (False, False, args)

           checkChecks args | "-c" `elem` args = (True, filter ("-c" /=) args)
                            | otherwise = (False, args)

           checkNumericArg s args =
               case span (s /=) args of
                 (args, [])              -> (Nothing, args)
                 (before, _ : d : after) -> (Just (read d), before ++ after)

           maybeWriteIORef Nothing _ = return ()
           maybeWriteIORef (Just v) r = writeIORef r v

           checkAfter args | null args        = (repl, args)
                           | "-i" `elem` args = (repl, filter ("-i" /=) args)
                           | otherwise        = (\_ _ _ -> return (), args)

--------------------------------------------------------------------------------

partitionTops [] = ([], [], [], [], [])
partitionTops (t:ts) =
    case t of
      Axiom a gfp   -> ((a, gfp):axioms, fds, preds, requirements, opacities)
      FunDep fd     -> (axioms, fd:fds, preds, requirements, opacities)
      Query p       -> (axioms, fds, p:preds, requirements, opacities)
      Requirement r -> (axioms, fds, preds, r:requirements, opacities)
      Opacity o     -> (axioms, fds, preds, requirements, o:opacities)
    where (axioms, fds, preds, requirements, opacities) = partitionTops ts

--------------------------------------------------------------------------------

qsolve axioms fds rqs ops (hypotheses :=> conclusions) =
    S.run (solveAnonymous Q { qAxioms           = axioms
                            , qFundeps          = fds
                            , qRequirements     = rqs
                            , qOpacities        = ops
                            , qGenerics         = (filter (("g_" ==) . take 2 . nameFrom) (vars conclusions), [])
                            , qTransparents     = []
                            , qUniformVariables = filter (("u_" ==) . take 2 . nameFrom) (vars conclusions)
                            , qHypotheses       = hypotheses
                            , qGoals            = conclusions })
    where nameFrom (Kinded (Ident n _ _) _) = n

--------------------------------------------------------------------------------

showResult showProofs showNodeCount qp result =
    case result of
      AnsProved evidence improvement _ nodes
          | qp == improvement ## qp ->
              "Yes" ++
              (if showProofs then " [" ++ intercalate ", " (map (ppx . snd) evidence) ++ "]" else "") ++
              (if showNodeCount then " <" ++ show nodes ++ ">" else "") ++
              cyclicWarning
          | otherwise ->
              "Yes" ++
              (if showProofs then " [" ++ intercalate ", " (map (ppx . snd) evidence) ++ "]" else "") ++
              " (improved to " ++ ppx (improvement ## qp) ++ ")" ++
              (if showNodeCount then " <" ++ show nodes ++ ">" else "") ++
              cyclicWarning
          where cyclicWarning | cyclic (map snd evidence) = " WARNING: CYCLIC PROOF"
                              | otherwise                 = ""
      AnsFailed _ nodes -> "No " ++ (if showNodeCount then " <" ++ show nodes ++ ">" else "")
      AnsStuck evidence remaining improvement nodes
          | qp == improvement ## qp ->
              (if showProofs
               then "[" ++ intercalate ", " [ppx v ++ ":" ++ ppx (improvement ## p) | (v, p) <- remaining] ++ "] remaining."
               else "[" ++ intercalate ", " (map (ppx . (improvement ##) . snd) remaining) ++ "] remaining.") ++
              (if showProofs then " [" ++ intercalate ", " (map (ppx . snd) evidence) ++ "]" else "") ++
              (if showNodeCount then " <" ++ show nodes ++ ">" else "")
          | otherwise ->
              (if showProofs
               then "[" ++ intercalate ", " [ppx v ++ ":" ++ ppx (improvement ## p) | (v, p) <- remaining] ++ "] remaining."
               else "[" ++ intercalate ", " (map (ppx . (improvement ##) . snd) remaining) ++ "] remaining.") ++
              (if showProofs then " [" ++ intercalate ", " (map (ppx . snd) evidence) ++ "]" else "") ++
              " (improved to " ++ ppx (improvement ## qp) ++ ")" ++
              (if showNodeCount then " <" ++ show nodes ++ ">" else "")

--------------------------------------------------------------------------------

run showProofs showNodeCount axioms fds requirements opacities fns =
    do results <- mapM runSet fileSets
       return (last results)

    where fileSets = iter fns
              where iter ss = let (set, rest) = break ("-r" ==) ss
                              in if null rest then [set] else set : iter (tail rest)

          runSet fns = do (errors, axioms', fds', requirements', opacities', preds) <- foldM f ([], axioms, fds, requirements, opacities, []) fns
                          mapM_ putStr errors
                          report (map ppx preds) (map (\p -> showResult showProofs showNodeCount p (qsolve axioms' fds' requirements' opacities' p)) preds)
                          return (axioms', fds', requirements', opacities')

          f (errors, axioms, fds, requirements, opacities, preds) fn =
              do (errors', axioms', fds', requirements', opacities', preds') <- parseFile showProofs fn axioms fds requirements opacities
                 return (errors ++ errors', axioms', fds', requirements', opacities', preds ++ preds')

report ss ts = mapM_ putStrLn [s ++ " : " ++ t | (s,t) <- zip ss' ts]
    where l = maximum (map length ss)
          ss' = map (padr l) ss
          padr l s = s ++ replicate n ' '
              where n = l - length s

reportWarnings ws = mapM_ putStrLn ws

reportRqImpls rqimpls
    | null s = return ()
    | otherwise = putStrLn s
    where s = ppx rqimpls

parseFile showProofs fn oldAxioms oldFDs oldRequirements oldOpacities =
    do s <- readFile fn
       let result = runParser (terminal (whiteSpace >> many top)) () fn s
       case result of
         Left err -> return ([show err ++ "\n"], oldAxioms, oldFDs, oldRequirements, oldOpacities, [])
         Right results -> let (newAxioms, newFDs, preds, newRequirements, newOpacities ) = partitionTops results
                              fds = mergeFDs newFDs oldFDs
                              ops = mergeOpacities newOpacities oldOpacities
                              ((requireErrors, requirements), warnings) = runV_ (mergeRequirements fds oldRequirements newRequirements)
                              addResult = runV (addAxioms oldAxioms fds requirements ops newAxioms)
                          in do reportWarnings warnings
                                case addResult of
                                  Left err -> return (requireErrors ++ [err], oldAxioms, fds, requirements, ops, preds)
                                  Right ((_, newAxioms, rqimpls), warnings') ->
                                      do reportWarnings warnings'
                                         when showProofs (reportRqImpls rqimpls)
                                         return (requireErrors, newAxioms, fds, requirements, ops, preds)

--------------------------------------------------------------------------------

repl showProofs showNodeCount (axioms, fds, requirements, opacities)
    = do hSetBuffering stdout NoBuffering
         loop showProofs showNodeCount axioms fds requirements opacities
    where loop showProofs showNodeCount axioms fds requirements opacities =
              do putStr "> "
                 s <- getLine
                 case dropWhile isSpace s of
                   "" -> loop showProofs showNodeCount axioms fds requirements opacities
                   "q" -> return ()
                   "r" -> loop showProofs showNodeCount [] O.fundeps [] []
                   "d" -> do printx fds ; printx axioms ; printx requirements ; printx opacities ; loop showProofs showNodeCount axioms fds requirements opacities
                   "t on" -> do writeIORef doTrace True
                                writeIORef doTraceInput True
                                loop showProofs showNodeCount axioms fds requirements opacities
                   "t off" -> do writeIORef doTrace False
                                 writeIORef doTraceInput False
                                 loop showProofs showNodeCount axioms fds requirements opacities
                   "p on" -> loop True showNodeCount axioms fds requirements opacities
                   "p off" -> loop False showNodeCount axioms fds requirements opacities
                   "n on" -> loop showProofs True axioms fds requirements opacities
                   "n off" -> loop showProofs False axioms fds requirements opacities
                   ('f' : ' ' : fn) ->
                       do (axioms', fds', requirements', opacities') <- run showProofs showNodeCount axioms fds requirements opacities [fn]
                          loop showProofs showNodeCount axioms' fds' requirements' opacities'
                   _ -> case runParser (terminal (whiteSpace >> top)) () "<interactive>" s of
                          Left err -> do print err ; loop showProofs showNodeCount axioms fds requirements opacities
                          Right (FunDep fd) -> loop showProofs showNodeCount axioms (mergeFDs [fd] fds) requirements opacities
                          Right (Axiom axiom gfp) ->
                              case runV (addAxioms axioms fds requirements opacities [(axiom, gfp)]) of
                                Left err -> do putStr err ; loop showProofs showNodeCount axioms fds requirements opacities
                                Right ((_, axioms', rqimpls), warnings) ->
                                    do reportWarnings warnings
                                       when showProofs (reportRqImpls rqimpls)
                                       loop showProofs showNodeCount axioms' fds requirements opacities
                          Right (Query qpreds) -> do putStrLn (showResult showProofs showNodeCount qpreds (qsolve axioms fds requirements opacities qpreds))
                                                     loop showProofs showNodeCount axioms fds requirements opacities
                          Right (Requirement r) ->
                              case runV_ (mergeRequirements fds requirements [r]) of
                                (([], rs), []) -> loop showProofs showNodeCount axioms fds rs opacities
                                ((errs, _), []) -> do mapM_ putStr errs ; loop showProofs showNodeCount axioms fds requirements opacities
                          Right (Opacity o) ->
                              loop showProofs showNodeCount axioms fds requirements (mergeOpacities [o] opacities)
