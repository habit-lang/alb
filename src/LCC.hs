module LCC (LCCOptions(..), lccompile, defaultLCCOptions) where

-- This file began as a copy of CompCert.hs

import Data.List
import Syntax.LC
import Printer.LC
import System.Process
import System.Environment
import System.Exit
import System.FilePath
import System.IO


-- Options for invoking the LC Compiler
data LCCOptions = LCCOptions { jarPath      :: Maybe String,
                               extraMilFiles :: [FilePath],
                               otherOptions :: String,
                               fake         :: Bool }

defaultLCCOptions = LCCOptions { jarPath      = Nothing,
                                 extraMilFiles = [],
                                 otherOptions = "",
                                 fake         = False }

lccompile :: LCCOptions -> String -> Program -> IO ()
lccompile lcco outputFileName prog =
    do writeFile lcFileName (show (ppr prog))
         -- java -cp "${CLASSPATH}" lc.LCC -S "${TMP}"
       execPath <- getExecutablePath
       let jarPath' = case jarPath lcco of
                        Nothing   -> takeDirectory execPath </> "mil-tools.jar"
                        Just path -> path
           lccCmd = intercalate " " $ [ "java",
                                        "-jar", jarPath' ] ++
                                      extraMilFiles lcco ++
                                      [ lcFileName,
                                        "-l" ++ llFileName,
                                        otherOptions lcco ]
       if fake lcco
       then putStrLn lccCmd
       else do exitCode <- system lccCmd
               if exitCode /= ExitSuccess
               then hPutStrLn stderr ("mil-tools invokation failed (" ++ show exitCode ++ ")")
               else return ()

    where lcFileName = replaceExtension outputFileName "lc"
          llFileName = replaceExtension outputFileName "ll"
