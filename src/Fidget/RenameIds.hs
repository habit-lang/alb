{-
  This module attempts to reduce the unique integer suffix on
  identifiers to a small value in an attempt to make the generated
  Fidget code easier to read.

  Fidget identifiers are in the form "Ident String Int" and are
  textually represented as "someName$1234" where the string part is
  called the 'prefix' and the integer part is the 'suffix'

  Properties of this transformation:
    All identifiers remain globally unique
    Zero-suffixed identifiers are not altered
    No explicitly renamed identifiers are altered (nb the --rename option)
    For each set of identifier prefixes exactly one resulting ident will have a zero-suffix
    Non-zero suffixes remain globally unique (this transform doesn't break the Eq/Ord instances)
    The smallest available suffix is always used
-}

module Fidget.RenameIds where

import Prelude hiding (pure)

import Common
import Control.Monad
import Control.Monad.Reader
import Data.Generics
import Data.List
import Fidget.AST hiding (Id)
import Syntax.Common (Id(..), toId)
import qualified Data.Map as M
import qualified Data.Set as S

renameIds :: Program -> Reader (M.Map Id Id) Program
renameIds = everywhereM (mkM (\i -> asks (M.findWithDefault i i)))

-- Acquire all Ids contained in a given tree.
getIdId :: Id -> [Id]
getIdId i = [i]

-- Synthesize an "Id" for the String in an external function
getIdFundec                            :: Fundec -> [Id]
getIdFundec (Internal f)                = []
getIdFundec (External (EFexternal i _)) = [toId i]
getIdFundec (External (EFbuiltin i _))  = [toId i]
getIdFundec (External _)                = []

getIds :: Program -> [Id]
getIds = everything (++) (mkQ [] getIdId `extQ` getIdFundec)

-- Build a mapping connecting the old Identifiers to the new values
--         rename one to PREFIX
--         rename the rest as "PREFIX${1,2,3..}"
idMapping :: (S.Set Id, Int, [Id]) -> Maybe ((Id,Id), (S.Set Id, Int, [Id]))
idMapping (_,_,[])                = Nothing
idMapping (s, cnt, id@(Ident prefix t f):is) = Just ((id, newId), (s', cnt', is))
  where
  newIdOptions = map (\n -> Ident prefix n f) (0:[cnt..])
  (newId:_) = dropWhile (`S.member` (S.delete id s)) newIdOptions
  s' = S.insert newId s
  cnt' = case newId of Ident _ c f -> max cnt c

-- Simplify all identifiers found in the given Fidget code but
-- are not members of the given ignore-list.
fixAllIds :: [Id] -> Program -> Program
fixAllIds ign x =
  let ignSet = S.fromList ign
      filterProtected = filter (\i -> i `S.notMember` ignSet) . S.toList
      ids = S.fromList (getIds x)
      newNamesMap = M.fromList
                  . unfoldr idMapping
                  $ (ids, 1, filterProtected ids)
  in runReader (renameIds x) newNamesMap

-- The top level entry for use by Driver.hs
fixIds :: [Id] -> Bool -> Pass () Program Program
fixIds _ False = pure id
fixIds exports True  = (pure . fixAllIds) exports
