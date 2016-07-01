module Parser (module Parser.Main, ParseM, chase, findFile) where

import Common
import Control.Monad.State
import Data.List (intercalate, isSuffixOf)
import Literate
import Parser.Main
import Parser.Lexer
import qualified Syntax.Surface as S
import System.Directory (doesFileExist)
import System.Exit
import System.FilePath (splitSearchPath, joinPath, (</>), (<.>))
import System.IO
import System.IO.Strict as Strict
import Text.Parsec (runParser)
import Text.Parsec.ByteString
import Text.Parsec.Indentation
import Text.Parsec.Indentation.Char

-- (For parser testing, try expressions of the form: parseString p "" string)

parseString   :: ParseM t -> String -> String -> Either String t
parseString p source contents
  = case runParser (terminal (localTokenMode (const Gt) p)) nullState source
           (mkIndentStream 0 maxBound False Any (mkCharIndentStream contents)) of
      Left err -> Left (show err)
      Right p  -> Right p

-- "Import chasing" mechanisms (using IO operations to read input files)

-- Search for an input file by exploring each of the paths in a given list:
findFile         :: [FilePath] -> String -> IO (Maybe FilePath)
findFile paths fn = firstExistingFile candidates
  where candidates = fn : [ path </> fn <.> ext | path <- paths, ext <- ["hb", "lhb"] ]
        firstExistingFile []       = return Nothing
        firstExistingFile (pn:pns) = do b <- doesFileExist pn
                                        if b then return (Just pn)
                                             else firstExistingFile pns

-- Read a program from a given path, eliminating literate comments if necessary:
readProgram :: FilePath -> IO (Either String S.Program)
readProgram path = do contents <- Strict.readFile path
                      if "lhb" `isSuffixOf` path
                        then return (delit path contents >>= parseString program path)
                        else return (parseString program path contents)

type Named   = (FilePath, Bool)              -- describes file to be loaded
type Loaded  = (FilePath, (Bool, S.Program)) -- describes file that has been loaded
type Loading = (Loaded, [FilePath])          -- describes file with pending dependencies

-- Load a collection of source programs starting from a given list of paths and
-- chasing explicit "requires" dependencies:
chase            :: [FilePath] -> [Named] -> Bool -> IO [Loaded]
chase paths named verbose = loadNamed [] named
 where
  -- If we are not currently loading a file, look at the next file that was
  -- named on the command line:
  loadNamed                  :: [Loaded] -> [Named] -> IO [Loaded]
  loadNamed loaded []         = return (reverse loaded)
  loadNamed loaded ((n,q):named)
     | n `isInLoaded` loaded  = loadNamed loaded named       -- already loaded?
     | otherwise              = loadFile n q loaded [] named -- start loading

  -- Start the process of loading a file, reading and parsing its source code
  -- so that we can extract the list of other files on which it depends.
  loadFile :: FilePath -> Bool -> [Loaded] -> [Loading] -> [Named] -> IO [Loaded]
  loadFile path q loaded loading named
    = do when verbose (putStrLn ("Reading \"" ++ path ++ "\":"))
         p <- readProgram path
         case p of
           Left err   -> do hPutStrLn stderr err
                            exitFailure
           Right prog -> do ds <- dependencies path (map (joinPath . S.dislocate) (S.requires prog))
                            when verbose (putStrLn ("  -- depends on {" ++ intercalate ", " ds ++ "}"))
                            continueLoading loaded named (((path, (q, prog)), ds):loading)

  -- Compute the list of path dependencies corresponding to a list of required names:
  dependencies :: FilePath -> [String] -> IO [FilePath]
  dependencies path []     = return []
  dependencies path (n:ns)
    = do md <- findFile paths n
         case md of
           Just d  -> (d:) `fmap` dependencies path ns
           Nothing -> do hPutStrLn stderr ("Cannot find " ++ show n ++ ", required by " ++ show path)
                         exitFailure

  -- Currently in the process of loading a particular file, which either has
  -- no remaining dependencies (so it can be loaded), or else has dependencies
  -- that need to be processed:
  continueLoading                :: [Loaded] -> [Named] -> [Loading] -> IO [Loaded]
  continueLoading loaded named [] = loadNamed loaded named
  continueLoading loaded named ((l,ds):loading)
                                  = loadDeps loaded named loading l ds

  -- Load dependencies before the file that requires them:
  loadDeps :: [Loaded] -> [Named] -> [Loading] -> Loaded -> [FilePath] -> IO [Loaded]
  loadDeps loaded named loading l []           -- no dependencies left; load file and continue
            = continueLoading (l:loaded) named loading
  loadDeps loaded named loading l (d:ds)
          | d `isInLoaded` loaded              -- dependency already loaded
            = loadDeps loaded named loading l ds
          | d `isInLoading` loading            -- dependency cycle
            = do hPutStrLn stderr ("Cyclic dependency in inputs: "
                                   ++ (intercalate " -> "
                                       (reverse
                                        (d : dropAfter d (fst l : map (fst . fst) loading)))))
                 exitFailure
          | otherwise
            = loadFile d (loudness d named) loaded ((l,ds):loading) named

  dropAfter        :: Eq a => a -> [a] -> [a]
  dropAfter x []    = []
  dropAfter x (y:ys)
        | x==y      = [y]
        | otherwise = y : dropAfter x ys

  -- Test to determine whether a given file path has already been loaded:
  isInLoaded      :: FilePath -> [Loaded] -> Bool
  isInLoaded n     = any ((==) n . fst)

  -- Test to determine whether a given file path is currently being loaded:
  isInLoading     :: FilePath -> [Loading] -> Bool
  isInLoading n    = any ((==) n . fst . fst)

  -- Copy the Loud/Quiet setting from the named files if it appears there:
  loudness        :: FilePath -> [Named] -> Bool
  loudness n named = case [ q | (n',q) <- named, n==n' ] of
                       (q : _) -> q      -- use specified Loud/Quiet setting if named
                       []      -> True   -- make quiet if n is not mentioned in named
