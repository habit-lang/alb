{-# LANGUAGE Rank2Types, OverloadedStrings, PatternGuards, TupleSections #-}
module Main where

import Prelude hiding ((<$>), pure)

import Control.Monad
import Data.IORef
import Data.Char
import Data.List (intercalate, nub)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isNothing)
import qualified Data.IntSet as Set
import System.Console.GetOpt
import System.Directory (doesFileExist)
import System.Environment (getArgs, getEnvironment, getProgName)
import System.Exit
import System.FilePath  ((</>), (<.>), dropExtension, joinDrive, splitSearchPath, takeFileName)
import System.IO

import Analyzer
import Common
import LC.LambdaCaseToLC
import LC.RenameTypes
import MILTools
import Normalizer.EtaInit
import Normalizer.Inliner
import Normalizer.PatternMatchCompiler
import Parser
import Printer.Common hiding (defaultOptions, showKinds, (</>))
import Printer.IMPEG
import Printer.LambdaCase
import Printer.LC
import Solver.Trace as Solver
import qualified Syntax.Surface as S
import Syntax.LC
import Syntax.MangleIds
import Syntax.XMPEG
import Specializer
import Typechecker
import qualified Typechecker.TypeInference as Inference (doTrace)
import Typechecker.LambdaCase (checkLCProgram)
import Typechecker.LambdaCasePropagation (propagateLCTypes)

import qualified Debug.Trace as Trace

-- Data structures for describing command line options/settings:

data Stage = Desugared
           | KindsInferred
           | TypesInferred
           | Specialized
           | Normalized
           | Annotated
           | LCed
           | LLVMed
           | Compiled
  deriving (Eq)

data Input = Quiet { filename :: String}
           | Loud  { filename :: String }

isQuiet:: Input -> Bool
isQuiet (Quiet _) = True
isQuiet _         = False

data Options = Options { stage                :: Stage
                       , searchPath           :: [FilePath]
                       , inputs               :: [Input]
                       , output               :: Maybe String
                       , initialize           :: Id
                       , prefix               :: String
                       , mainId               :: Maybe Id
                       , exports              :: [(Id, Id)]
                       , printExportSignatures:: Bool
                       , dotFiles             :: Bool
                       , simplifyNames        :: Bool
                       , milOptions           :: MILOptions
                       , populateEnvironments :: Bool
                       , traceSolver          :: Bool
                       , traceSolverInputs    :: Bool
                       , checkSolver          :: Bool
                       , checkSolverMaxDepth  :: Integer
                       , checkSolverMaxTrail  :: Int
                       , checkSolverMaxSimplIters :: Integer
                       , traceInference       :: Bool
                       , traceSpecialization  :: Bool
                       , showKinds            :: Bool
                       , verbose              :: Bool
                       , shortenInternalNames :: Bool
                       , noQuiet              :: Bool
                       , showHelp             :: Bool }

defaultOptions :: Options
defaultOptions = Options { stage                = Compiled
                         , searchPath           = [""]
                         , inputs               = []
                         , output               = Nothing
                         , initialize           = "initialize"
                         , prefix               = "hb_"
                         , mainId               = Just "main"
                         , exports              = []
                         , printExportSignatures= False
                         , dotFiles             = True
                         , simplifyNames        = False
                         , milOptions           = defaultMILOptions
                         , populateEnvironments = False
                         , traceSolver          = False
                         , traceSolverInputs    = False
                         , checkSolver          = False
                         , checkSolverMaxDepth  = 200
                         , checkSolverMaxTrail  = 1000
                         , checkSolverMaxSimplIters = 20
                         , traceInference       = False
                         , traceSpecialization  = False
                         , showKinds            = False
                         , verbose              = False
                         , shortenInternalNames = True
                         , noQuiet              = False
                         , showHelp             = False }

options :: [OptDescr (Options -> Options)]
options =
    [ Option [] ["Sd"] (NoArg (\opt -> opt { stage = Desugared }))
        "Stop after desugaring"

    , Option [] ["Sk"] (NoArg (\opt -> opt { stage = KindsInferred }))
        "Stop after kind inference"

    , Option ['t'] ["St"] (NoArg (\opt -> opt { stage = TypesInferred }))
        "Stop after type inference"

    , Option [] ["Ss"] (NoArg (\opt -> opt { stage = Specialized }))
        "Stop after specialization"

    , Option [] ["Sn"] (NoArg (\opt -> opt { stage = Normalized }))
        "Stop after MPEG normalization"

    , Option [] ["Sa"] (NoArg (\opt -> opt { stage = Annotated }))
        "Stop after lambda_case annotation"

    , Option [] ["Sc"] (NoArg (\opt -> opt { stage = LCed }))
        "Stop after generating LC"

    , Option [] ["Sl"] (NoArg (\opt -> opt{ stage = LLVMed }))
        "Stop after generating LLVM"

    , Option ['o'] [] (ReqArg (\out opt -> opt { output = Just out }) "FILE")
        "Write output to file"

    , Option ['q'] [] (ReqArg (\fn opt -> opt { inputs = Quiet fn : inputs opt }) "FILE")
        "Use FILE as input, but suppress file's output through typechecking"

    , Option ['i'] ["path"] (ReqArg (\path opt -> opt { searchPath = splitSearchPath path ++ searchPath opt }) "SEARCHPATH")
        "Set the search path for locating source files"

    , Option [] ["no-quiet"] (NoArg (\opt -> opt { noQuiet = True }))
        "Treat no required files as quiet"

    , Option [] ["trace-solver"] (NoArg (\opt -> opt { traceSolver = True }))
        "Generate debug tracing from solver"

    , Option [] ["trace-solver-inputs"] (NoArg (\opt -> opt { traceSolverInputs = True }))
        "Generate debug tracing of solver inputs"

    , Option [] ["trace-inference"] (NoArg (\opt -> opt { traceInference = True }))
        "Generate debug tracing from type inference"

    , Option [] ["check-solver"] (NoArg (\opt -> opt { checkSolver = True }))
        "Enable bug checks in solver"

    , Option [] ["solver-max-depth"] (ReqArg (\x opt -> opt { checkSolverMaxDepth = read x }) "DEPTH")
        "Maximum solver tree depth before bug check"

    , Option [] ["solver-max-trail"] (ReqArg (\x opt -> opt { checkSolverMaxTrail = read x }) "LENGTH")
        "Maximum solver trail length before bug check"

    , Option [] ["solver-max-simpl-iters"] (ReqArg (\x opt -> opt {checkSolverMaxSimplIters = read x }) "ITERS")
        "Maximum iterations in instance simplification before bug check"

    , Option [] ["trace-specialization"] (NoArg (\opt -> opt { traceSpecialization = True }))
        "Generate debug tracing from specialization"

    , Option [] ["show-kinds"] (NoArg (\opt -> opt { showKinds = True }))
        "Show kind annotations in intermediate stages"

    , Option [] ["init"] (ReqArg (\init opt -> opt { initialize = fromString init }) "INIT_FUN")
        "Name of the generated initializer function"

    , Option [] ["habit-prefix"] (ReqArg (\x opt -> opt { prefix = x }) "STRING")
        "Prefix to place before non-exported functions"

    , Option ['e'] ["export"] (ReqArg (\x opt ->
                                           opt { exports =
                                                     let splitString s =
                                                             case break (',' ==) s of
                                                               (_, []) -> [s]
                                                               (s', ',':rest) -> s' : splitString rest
                                                         exportFrom s =
                                                             case break (':' ==) s of
                                                               (_, []) -> (toId s, toId s)
                                                               (s', ':':s'') -> (toId s', toId s'')
                                                     in map exportFrom (splitString x) ++ exports opt }) "IDENT:IDENT,...")
        "TODO"

    , Option [] ["main-is"] (ReqArg (\x opt -> opt { mainId = Just (toId x) }) "MAIN")
        "Name of main entry point (assumed to be 'main' if this option is not specified)"

    , Option [] ["no-main"] (NoArg (\opt -> opt { mainId = Nothing }))
        "Generates no main entry point"

    , Option [] ["print-export-signatures"] (NoArg (\opt -> opt { printExportSignatures = True }))
         "Print the C signatures of any exports"

    , Option [] ["no-dot-files"] (NoArg (\opt -> opt { dotFiles = False } ))
        "Does not include preferences from any previously checked dot files"

    , Option [] ["mil-jar"] (ReqArg (\x opt -> opt { milOptions = (milOptions opt) { MILTools.jarPath = Just x } }) "PATH")
         "Path to the MIL-tools JAR file"

    , Option [] ["llvm-main"] (ReqArg (\x opt -> opt{ milOptions = (milOptions opt){ MILTools.llvmMain = Just x }}) "STRING")
           "Name of the main/initialization function to be generated in LLVM"

    , Option [] ["mil-opt"] (ReqArg (\x opt -> opt { milOptions = (milOptions opt) { MILTools.otherOptions = x ++ otherOptions (milOptions opt) }}) "STRING")
          "Other options to MIL-tools"

    , Option [] ["include-mil"] (ReqArg (\x opt -> opt{ milOptions = (milOptions opt){ extraMilFiles = extraMilFiles (milOptions opt) ++ [x] } }) "FILE")
          "Additional MIL files to pass to MIL-tools"

    , Option [] ["fake-mil"] (NoArg (\opt -> opt { milOptions = (milOptions opt) { MILTools.fake = True } }))
          "Generate LC output and MIL-tools command, but do not actually invoke MIL-tools"

    , Option [] ["clang"] (ReqArg (\x opt -> opt{ milOptions = (milOptions opt){ clangPath = Just x } }) "FILE")
          "Path to clang binary (or replacement script)"

    , Option [] ["clang-opt"] (ReqArg (\x opt -> opt{ milOptions = (milOptions opt){clangOptions = x ++ clangOptions (milOptions opt) }}) "STRING")
          "Other options to clang"

    , Option [] ["verbose"] (NoArg (\opt -> opt { verbose = True }))
         "Be verbose"

    , Option [] ["show-internal-names"] (NoArg (\opt -> opt { shortenInternalNames = False }))
         "Show internal names for MPEG identifiers"

    , Option ['?'] ["help"] (NoArg (\opt -> opt { showHelp = True }))
        "Show usage information, then exit" ]

-- Additional sources of options

readDotFiles :: IO [Options -> Options]
readDotFiles =
    do albName <- dropExtension `fmap` getProgName
       homeDirectory <- getHomeDirectory
       homeDirectoryOptions <-
           case homeDirectory of
             Just dir -> readDotFile (dir </> "" <.> albName)
             Nothing  -> return [id]
       currentDirectoryOptions <- readDotFile ("." </> "" <.> albName)
       if dotFiles (foldl (flip ($)) defaultOptions currentDirectoryOptions)
       then return (homeDirectoryOptions ++ currentDirectoryOptions)
       else return currentDirectoryOptions

    where getHomeDirectory =
              do env <- getEnvironment
                 let home = lookup "HOME" env
                 case home of
                   Just homeDir -> return (Just homeDir)
                   Nothing -> let homeDrive = lookup "HOMEDRIVE" env
                                  homePath  = lookup "HOMEPATH" env
                              in case (homeDrive, homePath) of
                                   (Just homeDrive', Just homePath') -> return (Just (joinDrive homeDrive' homePath'))
                                   _ -> return Nothing

          readDotFile fn =
              do exists <- doesFileExist fn
                 if not exists
                 then return [id]
                 else do s <- readFile fn
                         let (optBuilders, [], errors) = getOpt (ReturnInOrder loud) options (splitAsCommandLine s)
                                 where loud fn opts = opts { inputs = Loud fn : inputs opts }
                         if (not (null errors))
                         then do mapM_ (hPutStrLn stderr) (("Errors in configuration file " ++ fn) : errors)
                                 return [id]
                         else return optBuilders

          splitAsCommandLine s =
              case dropWhile isSpace s of
                [] -> []
                ('"' : s') -> let (this, rest) = break ('"'==) s'
                              in case rest of
                                   ('"' : rest') -> this : splitAsCommandLine rest'
                                   _ -> error "Malformed options string in dot file: unable to find closing double quote"
                ('\'' : s') -> let (this, rest) = break ('\''==) s'
                               in case rest of
                                    ('\'' : rest') -> this : splitAsCommandLine rest'
                                    _ -> error "Malformed options string in dot file: unable to find closing quote"
                s' -> let (this, rest) = span isNonSpace s'
                      in this : splitAsCommandLine rest
              where isNonSpace c = not (isSpace c || c == '"' || c == '\'')

-- Main compiler pipeline:

buildPipeline :: Options -> Pass () [(String, (Bool, S.Program))] (IO ())
buildPipeline options =
    case stage options of
      Desugared        -> filePipe $ \s q -> toDesugar
      KindsInferred    -> filePipe $ \s q -> toInferKinds
      TypesInferred    -> filePipe $ \s q -> toInferTypes s >=> pure fst
      Specialized      -> codePipe toSpecialized
      Normalized       -> codePipe toNormalized
      Annotated        -> codePipe toAnnotated
      LCed             -> codePipe toLCed
      LLVMed           -> case output options of
                            Nothing -> error "How do we not have an output name?"
                            Just s  -> toLCed >=> pure (milCompile (milOptions options) s False)
      Compiled         -> case output options of
                            Nothing -> error "How do we not have an output name?"
                            Just s  -> toLCed >=> pure (milCompile (milOptions options) s True)

    where filePipe' = initial initialState . mapM . (\f -> \(s, (q, p)) -> f s q p)

          codePipe f = f >=> pure (withShowKinds (showKinds options) . ppr) >=> writeIntermediate
          filePipe f = filePipe' (\s q -> f s q >=> printFile q) >=> pure vcat >=> writeIntermediate

          printFile quiet | quiet && not (noQuiet options) = pure (const empty)
                          | otherwise = pure (withShortenedNames (shortenInternalNames options) . withShowKinds (showKinds options) . ppr)

          exported :: [(Id, Bool)]
          exported = nub (maybe id (:) ((, True) `fmap` mainId options) (map ((, False) . fst) (exports options)))

          toDesugar
            = fixityProgram >=> freshenProgram >=> eliminateTuplesProgram >=>
              desugarLabeledFields >=> desugarProgram >=> patternTuplesProgram >=>
              generateTuples >=> rewriteFunctionalNotation

          toInferKinds
            = toDesugar >=> inferKinds

          toInferTypes s
            = toInferKinds >=> inferTypes s >=>
              first cleanupProgram

          toSpecialized
            = filePipe' (\s q -> toInferTypes s) >=> pure concat' >=> specializeProgram exported

          toNormalized
            = toSpecialized >=> patternMatch >=> pure (inlineProgram exported) >=> pure etaInit

          toAnnotated
            = toNormalized >=> propagateLCTypes >=> checkLCProgram

          toLCed
            | Nothing <- mainId options = error "Unable to generate LC without main"
            | Just main <- mainId options =
                toAnnotated >=> pure etaInit >=> pure (inlineProgram exported) >=>
                LC.RenameTypes.renameProgramCtors >=> LC.RenameTypes.renameProgramTypes >=>
                lambdaCaseToLC (Entrypoints exported) >=> mangleProgram

          writeIntermediate =
              pure (\d -> case output options of
                            Nothing -> putStrLn (show d)
                            Just s -> do when (verbose options) (putStrLn ("Writing \"" ++ s ++ "\":"))
                                         writeFile s (show d))

          emptyDesugaringState :: ((((S.Fixities, ScopeEnv),
                                     DesugaringState),
                                    TupleState),
                                   LabeledFields)
          emptyDesugaringState = ((((S.Fixities Map.empty Map.empty, ([], [])),
                                    ([], ([], []))),
                                   (Set.empty, Set.empty)),
                                  emptyLabeledFields)

          initialState = (((emptyDesugaringState,
                            emptyFunctionalNotationState),
                           emptyKindInferenceState),
                          emptyTypeInferenceState)

          concat' ps = (concatPrograms programs, (Map.unions ctorEnvs, last solverEnvironments))
              where (programs, ps') = unzip ps
                    (ctorEnvs, solverEnvironments) = unzip ps'

main = do args <- getArgs
          dotFileOptBuilders <- readDotFiles
          let (optBuilders, [], errors) = getOpt (ReturnInOrder loud) options args
                where loud fn opts = opts { inputs = Loud fn : inputs opts }
              clOpts                    = foldl (flip ($)) defaultOptions optBuilders
              opts                      = if dotFiles clOpts
                                          then foldl (flip ($)) defaultOptions (dotFileOptBuilders ++ optBuilders)
                                          else clOpts
              paths                     = searchPath opts

          inps <- mapM (\input -> do let fn = filename input
                                     path <- findFile paths fn
                                     return (fn, path, isQuiet input)) (reverse (inputs opts))

          when (showHelp opts) $
               do hPutStrLn stderr (usageInfo "Usage: alb [OPTION...] FILES..." options)
                  exitSuccess

          let errors' = [ "No inputs specified"                 | null (inputs opts) ]
                     ++ [ "Cannot find input for " ++ show name | (name, Nothing, _) <- inps ]
                     ++ [ "Empty search path"                   | null paths ]
                     ++ errors

          when (not (null errors')) $
               do mapM_ (hPutStrLn stderr) errors'
                  exitFailure

          writeIORef Solver.doTrace (traceSolver opts)
          writeIORef Solver.doTraceInput (traceSolverInputs opts || traceSolver opts)
          writeIORef Solver.doCheck (checkSolver opts)
          writeIORef Solver.checkSolverTreeDepth (checkSolverMaxDepth opts)
          writeIORef Solver.checkTrailLength (checkSolverMaxTrail opts)
          writeIORef Solver.checkSimplificationIterations (checkSolverMaxSimplIters opts)
          writeIORef Inference.doTrace (traceInference opts)
          writeIORef Specializer.doTrace (traceSpecialization opts)

          pipelineInput <- chase paths [ (path, q) | (_, Just path, q) <- inps ] (verbose opts)

          let printMessage d = show (withShortenedNames (shortenInternalNames opts) (withShowKinds (showKinds opts) (ppr d)))

              showWarnings warnings
               = when (not (null warnings))
                   (mapM_ (hPutStrLn stderr . printMessage) warnings)

              opts' | stage opts == Compiled || stage opts == LLVMed =
                        case output opts of
                          Just _ -> opts
                          Nothing -> let (_, Just file, _) = head inps in
                                     opts{ output = Just (dropExtension (takeFileName file)) }
                    | otherwise = opts

          case runPass (buildPipeline opts') pipelineInput (1, ()) of
            Left (err, warnings)     -> do showWarnings warnings
                                           hPutStrLn stderr (printMessage err)
                                           exitFailure
            Right (act, warnings, _) -> do showWarnings warnings
                                           act
