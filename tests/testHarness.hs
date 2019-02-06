import Control.Monad
import System.Environment
import System.Exit
import System.Process
import Text.Printf
import System.IO

testFile :: String -> IO [(String, Int)]
testFile f = do
  putStrLn $ "Testing " ++ f ++ ": "
  hFlush stdout
  code <- rawSystem f []
  x <- return $ case code of
                  ExitSuccess   -> []
                  ExitFailure x -> [(f, x)]
  putStr "\n"
  return x

summary files failedFiles = do
  printf "Summary: %d of %d files passed, %d tests failed\n"
             (length files - length failedFiles :: Int)
             (length files :: Int)
             (sum $ map snd failedFiles :: Int)

reportFile (file, failures) = do
  printf "  Failed: %s (failed %d tests)\n" (file :: String) (failures :: Int)

main = do
  files <- getArgs
  putStrLn $ take 72 $ repeat '='
  failedFiles <- liftM concat $ mapM testFile files
  putStrLn $ take 72 $ repeat '='
  summary files failedFiles
  mapM reportFile failedFiles
  return ()
