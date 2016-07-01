{-# LANGUAGE DeriveDataTypeable, OverloadedStrings #-}

{-
This is "albc" - shell script like Haskell glue for
the alb, ccomp, assembler (gcc), and linker (ld) stages
of Habit compilation.

## USE ## 

0) cabal install

1) Make a file "$(HOME)/.albc" with an entry of: 

    base = "/path/to/hasp/dir/and/keep/the/quotes"

2) If you want to use non-standard locations for your alb, ccomp,
harness.o, chenny.o, assembler, or linker then add the appropriate
full-path to ".albc" (identifiers: "alb', "ccomp", "harness", "gcObj",
"as", and "ld")

3) Be sure you're chenny.o and harness.o objects exist (use the existing
makefiles)

4) run: albc some-habit-code.hb ; ./some-habit-code.elf

## NOTES ##
The include directory is just the local directory (hardcoded).  Both
the assembler and linker are executed as shell commands (1 string that
includes the command and arguments) as those are unlikely to see change.

It's all rather 20-minute-hack-job style - feel free to make modifications.

-}

import System.Console.CmdArgs
import System.Console.CmdArgs.Explicit (helpText, HelpFormat(..))
import System.Console.CmdArgs.Text
import System.IO.Temp
import System.Cmd (rawSystem, system)
import System.Exit (ExitCode(..))
import System.Directory (getCurrentDirectory, doesFileExist)
import System.FilePath (joinPath, addExtension, dropExtension)
import Data.Configurator
import Data.Configurator.Types
import Data.Maybe
import Control.Monad
import qualified Data.Text as T

setExtension f = addExtension (dropExtension f)

-- Relative offsets:
gcRel    = joinPath . (: ["compcert1.8.2-hasp/runtime/gc/cheney.o"])
albRel   = joinPath . (: ["habitat/compiler/alb"])
ccompRel = joinPath . (: ["compcert1.8.2-hasp/ccomp"])
harnessRel = joinPath . (:["compcert1.8.2-hasp/test/fidget/harness.o"])

-- Defaults for assember and linker
defAS = "gcc -c -m32"
defLD = "gcc -g -Wall -m32"

-- Obtain paths for: compilers, assember, linker, and object files.
getPaths :: Maybe String -> 
            Config       ->
            IO (FilePath,FilePath,FilePath,FilePath,FilePath,FilePath)
getPaths mBase cfg = do
  base <- lookupDefault (error "No base provided and not all the needed paths are explicit") cfg "base"
  getPathsWithBase (fromMaybe base mBase) cfg

getPathsWithBase :: String -> 
                    Config ->
                    IO (FilePath,FilePath,FilePath,FilePath,FilePath,FilePath)
getPathsWithBase base cfg = do

  -- FIXME should ask for chenny.cmp and compile from there?
  gcObj <- lookupDefault (gcRel base) cfg "gcObj"
  alb   <- lookupDefault (albRel base) cfg "alb"
  ccomp <- lookupDefault (ccompRel base) cfg "ccomp"
  as    <- lookupDefault defAS cfg "as"
  ld    <- lookupDefault defLD cfg "ld"

  -- FIXME should ask for harness.c and compile from there?
  harnessObj <- lookupDefault (harnessRel base) cfg "harness"
  return (alb,ccomp,gcObj,as,ld,harnessObj)

data Args = Args 
        { inputFile    :: String
        , outputFile   :: Maybe String
--        , albOptions   :: String
--        , ccompOptions :: String
        , optimize     :: Maybe Int
        , basePath     :: Maybe String
        } deriving (Show, Data, Typeable)

defArgs = Args { inputFile  = def &= args
               , outputFile = def &= help "Output executable filename" &= explicit &= name "o" &= typ "FILE"
               , optimize   = def &= help "Optimization Level" &= explicit &= name "O"
               , basePath   = def &= help "Root of the HASP directory (override config)" &= typ "DIR" }
         &= summary "albc v1 - Compiles Habit to ia32 machine code"

main = do
 withTempDirectory "" "albc" $ \tDir -> do
   args <- cmdArgs defArgs
   let mode = cmdArgsMode defArgs
       file = inputFile args
   when (null file) (putStrLn $ showText defaultWrap $ helpText [] HelpFormatAll mode)
   b <- doesFileExist file
   when (not b) (error $ "No such file or directory: " ++ file)

   cfg  <- load [Optional "$(HOME)/.albc"]
   cwd <- getCurrentDirectory
   (albExe, ccompExe, gcObj, asExe, ldExe, harnessObj) <- getPaths (basePath args) cfg
   let out = fromMaybe (joinPath [cwd, setExtension file ".elf"]) (outputFile args)

       -- Obtain intermediate files
       baseTmp = addExtension (joinPath [tDir,file])
       fidgetFile = baseTmp ".fidget"
       objFile    = baseTmp ".o"
       sFile    = baseTmp ".s"

       -- Parse remaining options
       opt = fmap ((++) "-O" . show) . maybeToList . optimize $ args
       incDir = cwd --fixme add an option for more here
       main = "main" --fixme add an option

       -- Arguments (notice each element is a separate argument except for AS and LD)
       albArgs = ["-f" ++ main, "--rename=main,hbMain", "--rename=main0,hbMain0", "-o" ++ fidgetFile, "-i" ++ incDir] ++ opt ++ [file]
       ccompArgs = ["-S", "-o", sFile, fidgetFile]
       asArgs = ["-g", "-o" ++ objFile, sFile]
       ldArgs = ["-o" ++ out, objFile, harnessObj, gcObj]

       asCmd = unwords $ asExe : asArgs
       ldCmd = unwords $ ldExe : ldArgs
   
   albRet   <- rawSystem albExe albArgs
   when (albRet /= ExitSuccess) (error $ "The alb command (" ++ unwords (albExe:albArgs) ++ " ) failed: " ++ show albRet)

   ccompRet <- rawSystem ccompExe ccompArgs
   when (ccompRet /= ExitSuccess) (error $ "The ccomp command (" ++ unwords (ccompExe:ccompArgs) ++ ") failed: " ++ show ccompRet)

   asRet <- system asCmd
   when (asRet /= ExitSuccess) (error $ "assember failed: " ++ asCmd)

   ldRet <- system ldCmd
   when (ldRet /= ExitSuccess) (error $ "linker failed: " ++ ldCmd)
