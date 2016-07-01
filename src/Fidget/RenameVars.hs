{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Fidget.RenameVars (renameVars) where

-- Adds a prefix to non-exported variables so they don't conflict with
-- C code that we might link with

import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.Generics
import Data.List
import qualified Data.Map as Map

import Common
import Printer.Common ((<+>), text)
import Printer.Surface
import Syntax.Common
import Fidget.AST hiding (Id)

type M a = ReaderT (Map.Map Id Id) (PassM ()) a

renameVars :: String -> Pass () Program Program
renameVars prefix p@(Program globals funcs _ _ _ areas _) = do
  let oldIds = nub $ concat [map fst globals, [id | (id, Internal _) <- funcs], map (\(x,_,_,_) -> x) areas]
      newIds = map (renameId prefix) oldIds
  p' <- runReaderT (renames p) (Map.fromList $ zip oldIds newIds)
  return p'

renameId :: String -> Id -> Id
renameId prefix id
  | id /= freshPrefix id 0 = id
  | otherwise = fromString (prefix ++ fromId id)

renamesId :: Id -> M Id
renamesId id = do env <- ask; return (Map.findWithDefault id id env)

renameEverywhere :: (Data a) => a -> M a
renameEverywhere = everywhereM (mkM renamesId)

renames :: Program -> M Program
renames (Program globals funs main init types areas structs) =
    return Program `ap`
      renameEverywhere globals `ap`
      renameEverywhere funs `ap`
      renameEverywhere main `ap` 
      renameEverywhere init `ap` 
      return types `ap`
      renameEverywhere areas `ap` 
      return structs

