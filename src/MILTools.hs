module MILTools (MILOptions(..), milCompile, defaultMILOptions) where

-- This file began as a copy of CompCert.hs

import Data.List
import Data.Maybe
import Printer.LC
import Syntax.Common(fromId)
import Syntax.LC
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.Process


-- Options for invoking the LC Compiler
data MILOptions = MILOptions { jarPath       :: Maybe FilePath,
                               llvmMain      :: Maybe String,
                               extraMilFiles :: [FilePath],
                               otherOptions  :: String,
                               clangPath     :: Maybe FilePath,
                               clangOptions  :: String,
                               fake          :: Bool }

defaultMILOptions = MILOptions { jarPath       = Nothing,
                                 llvmMain      = Nothing,
                                 extraMilFiles = [],
                                 otherOptions  = "",
                                 clangPath     = Nothing,
                                 clangOptions  = "",
                                 fake          = False }

milCompile :: MILOptions -> String -> Bool -> Program -> IO ()
milCompile milo outputFileName invokeClang prog =
    do writeFile lcFileName (show (ppr prog))
       execPath <- getExecutablePath

       let jarPath' = fromMaybe (takeDirectory execPath </> "mil-tools.jar") (jarPath milo)
           milCmd = intercalate " " $ [ "java",
                                        "-jar", jarPath' ] ++
                                      extraMilFiles milo ++
                                      [ lcFileName,
                                        "-l" ++ llFileName,
                                        "--mil-main=" ++ main,
                                        maybe "" ("--llvm-main=" ++) (llvmMain milo),
                                        otherOptions milo ]
           main = fromId (head [ id | (id, b) <- fromEntrypoints (entrypoints prog), b ])
           clang = fromMaybe ("clang") (clangPath milo)
           exeName = replaceExtension outputFileName (takeExtension execPath)
           clangCmd = intercalate " " [ clang,
                                        "-o", exeName,
                                        llFileName ]

       if fake milo
       then putStrLn milCmd
       else do exitCode <- system milCmd
               if exitCode /= ExitSuccess
               then hPutStrLn stderr ("mil-tools invocation failed (" ++ show exitCode ++ ")")
               else do removeFile lcFileName
                       if invokeClang
                       then do exitCode <- system clangCmd
                               if exitCode /= ExitSuccess
                               then hPutStrLn stderr ("clang invocation failed (" ++ show exitCode ++")")
                               else removeFile llFileName
                       else return ()

    where lcFileName = replaceExtension outputFileName "lc"
          llFileName = replaceExtension outputFileName "ll"
