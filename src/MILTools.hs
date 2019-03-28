module MILTools (MILOptions(..), milCompile, defaultMILOptions) where

-- This file began as a copy of CompCert.hs

import Data.List
import Data.Maybe
import LC
import Printer.Common (Doc)
import Syntax.Common(fromId)
import Syntax.Specialized
-- import Syntax.Specialized as Specialized
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.Process


-- Options for invoking the LC Compiler
data MILOptions = MILOptions { milcPath      :: Maybe FilePath,
                               llvmMain      :: Maybe String,
                               extraMilFiles :: [FilePath],
                               otherOptions  :: String,
                               clangPath     :: Maybe FilePath,
                               clangOptions  :: String,
                               fake          :: Bool }

defaultMILOptions = MILOptions { milcPath      = Nothing,
                                 llvmMain      = Nothing,
                                 extraMilFiles = [],
                                 otherOptions  = "",
                                 clangPath     = Nothing,
                                 clangOptions  = "",
                                 fake          = False }

milCompile :: MILOptions -> String -> Bool -> (Doc, [(Id, Bool)]) -> IO ()
milCompile milo outputFileName invokeClang (prog, entrypoints) =
    do writeFile lcFileName (show prog)
       execPath <- getExecutablePath

       let milc = fromMaybe "milc" (milcPath milo)
           milCmd = intercalate " " $ [ milc ] ++
                                      extraMilFiles milo ++
                                      [ lcFileName,
                                        "-l" ++ llFileName,
                                        "--mil-main=" ++ main,
                                        maybe "" ("--llvm-main=" ++) (llvmMain milo),
                                        otherOptions milo ]
           main = fromId (head [ id | (id, b) <- entrypoints, b ])
           clang = fromMaybe "clang" (clangPath milo)
           exeName = replaceExtension outputFileName (takeExtension execPath)
           clangCmd = intercalate " " [ clang,
                                        "-o", exeName,
                                        clangOptions milo,
                                        llFileName ]

       if fake milo
       then putStrLn milCmd
       else runExternal milCmd
            (do removeFile lcFileName
                runExternal clangCmd
                  (removeFile llFileName))

    where lcFileName = replaceExtension outputFileName "lc"
          llFileName = replaceExtension outputFileName "ll"

runExternal :: String -> IO () -> IO ()
runExternal cmd next =
  do exitCode <- system cmd
     case exitCode of
       ExitSuccess -> next
       _           -> showError cmd exitCode

showError :: String -> ExitCode -> IO ()
showError msg code = hPutStrLn stderr (msg ++ " (" ++ show code ++ ")")
