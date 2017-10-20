{-# LANGUAGE DoAndIfThenElse #-}
module CompCert (CompCertOptions(..), compile, defaultCompCertOptions) where

import Data.List
import Fidget.AST
import Fidget.Pretty (pprogram)
import System.Process
import System.Exit
import System.FilePath
import System.IO

-- Options for invoking the CompCert C compiler
data CompCertOptions = CCO { root :: String,
                             ccompExe :: String,
                             harness :: String,
                             gc :: String,
                             otherOptions :: String,
                             fake :: Bool }


defaultCompCertOptions = CCO { root = ".",
                               ccompExe = "ccomp",
                               harness = "test" </> "fidget" </> "harness.c",
                               gc = "runtime" </> "gc" </> "cheney.o",
                               otherOptions = "",
                               fake = False }

compile :: CompCertOptions -> String -> Program -> IO ()
compile cco outputFileName prog =
    do writeFile fidgetFileName (show (pprogram prog))
       let ccompCmd = intercalate " " [ root cco </> ccompExe cco,
                                        "-L" ++ (root cco </> "lib" </> "compcert"),
                                        "-o " ++ outputFileName,
                                        fidgetFileName,
                                        root cco </> harness cco,
                                        root cco </> gc cco,
                                        otherOptions cco ]
       if fake cco
       then putStrLn ccompCmd
       else do exitCode <- system ccompCmd
               if exitCode /= ExitSuccess
               then hPutStrLn stderr ("ccomp invocation failed (" ++ show exitCode ++ ")")
               else return ()
    where fidgetFileName = replaceExtension outputFileName "fidget"
