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
data LCCOptions = LCCOptions { root         :: Maybe String,
                               otherOptions :: String,
                               fake         :: Bool }


defaultLCCOptions = LCCOptions { root         = Nothing,
                                 otherOptions = "",
                                 fake         = False }

lccompile :: LCCOptions -> String -> Program -> IO ()
lccompile lcco outputFileName prog =
    do writeFile lcFileName (show (ppr prog))
       withFile outputFileName WriteMode $ \ h -> do
         -- java -cp "${CLASSPATH}" lc.LCC -S "${TMP}"
         execPath <- getExecutablePath
         let rt     = case root lcco of
                           Nothing   -> takeDirectory execPath </> ".." </> "mil" 
                           Just path -> path
             lccCmd = intercalate " " [ "java",
                                        "-cp", rt </> "bin",
                                        "lc.LCC",
                                        "-S", lcFileName,
                                        otherOptions lcco ]
         if fake lcco
         then putStrLn $ lccCmd ++ " > " ++ outputFileName
         else do (_, _, _, ph) <- createProcess $ (shell lccCmd) { std_out = UseHandle h }
                 exitCode <- waitForProcess ph
                 if exitCode /= ExitSuccess
                 then hPutStrLn stderr ("lcc invokation failed (" ++ show exitCode ++ ")")
                 else return ()
    where lcFileName = replaceExtension outputFileName "lc"
