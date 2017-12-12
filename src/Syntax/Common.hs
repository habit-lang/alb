{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses, DeriveDataTypeable #-}
module Syntax.Common (module Syntax.Common, SourcePos, newPos, fromString) where

import Data.Char
import Data.Generics hiding (Fixity)
import Data.List
import GHC.Exts (IsString(..), fromString)
import Text.Parsec.Pos

--

data Assoc = LeftAssoc | RightAssoc | NoAssoc
             deriving (Eq, Show, Typeable, Data)

data Fixity = Fixity Assoc Int
              deriving (Eq, Show, Typeable, Data)

data Id = Ident String Int (Maybe Fixity)
          deriving (Show, Typeable)

instance Eq Id
    where Ident s n _ == Ident s' n' _
              | n == 0 && n' == 0 = s == s'
              | otherwise         = n == n'

instance Ord Id
    where compare (Ident s n _) (Ident s' n' _)
              | n == 0 && n' == 0 = compare s s'
              | otherwise         = compare n n'

instance Data Id where
  gfoldl k z id = z id
  gunfold k z id = undefined
  toConstr = undefined
  dataTypeOf = undefined

instance IsString Id
    where fromString = toId

toId   :: String -> Id
toId s  = Ident s 0 Nothing

fromId :: Id -> String
fromId (Ident s 0 f) = s
fromId (Ident s n f) = s ++ '$' : base36 n
    where base36 n | x == 0 = [letters !! y]
                   | otherwise = base36 x ++ [letters !! y]
              where (x, y) = n `divMod` 36
                    letters = ['0'..'9'] ++ ['a'..'z']


isConId :: Id -> Bool
isConId (Ident (c:_) _ _) = isUpper c || c == ':'

isTyConId :: Id -> Bool
isTyConId (Ident s@(c:_) _ _) = isUpper c || all (not . isAlphaNum) s

freshPrefix :: Id -> Int -> Id
freshPrefix (Ident s _ f) n = Ident s n f

setFixity :: Fixity -> Id -> Id
setFixity f (Ident s n _) = Ident s n (Just f)

getFixity :: Id -> Maybe Fixity
getFixity (Ident _ _ f) = f

--

data Literal = BitVector Integer Int
             | Numeric Integer
               deriving (Eq, Show, Typeable, Data)

--

data Kind = KVar Id
          | KFun Kind Kind
          | KStar
          | KNat
          | KArea
          | KLabel
            deriving (Eq, Show, Typeable, Data)

data KScheme t = ForallK [Id] t deriving (Eq, Show, Typeable, Data)

data Kinded t = Kinded t Kind
                deriving (Show, Typeable, Data)

type KId = Kinded Id

kind :: Kinded t -> Kind
kind (Kinded _ k) = k

instance Eq t => Eq (Kinded t)
    where Kinded t _ == Kinded t' _ = t == t'

instance Ord t => Ord (Kinded t)
    where compare (Kinded t _) (Kinded t' _) = compare t t'

unzipKinded :: [Kinded t] -> ([t], [Kind])
unzipKinded kxs = unzip [(x, k) | Kinded x k <- kxs]

--

data Location = Location { start, end :: SourcePos }
   deriving (Eq, Ord, Typeable, Data)

instance Show Location
    where show (Location start end)
              | sourceName start /= sourceName end     = sourceName start ++ ':' : show (sourceLine start) ++ ':' : show (sourceColumn start) ++ '-' :
                                                         sourceName end ++ ':' : show (sourceLine end) ++ ':' : show (sourceColumn end)
              | sourceLine start /= sourceLine end     = sourceName start ++ ':' : show (sourceLine start) ++ ':' : show (sourceColumn start) ++ '-' :
                                                         show (sourceLine end) ++ ':' : show (sourceColumn end)
              | sourceColumn start /= sourceColumn end = sourceName start ++ ':' : show (sourceLine start) ++ ':' : show (sourceColumn start) ++ '-' : show (sourceColumn end)
              | otherwise                              = sourceName start ++ ':' : show (sourceLine start) ++ ':' : show (sourceColumn start)

data Located t = At Location !t
               deriving (Eq, Show, Typeable, Data)

instance Functor Located
    where fmap f (At p t) = At p (f t)

at :: Located t -> u -> Located u
at (At p _) u = At p u

dislocate :: Located t -> t
dislocate (At _ t) = t

introducedPosition :: SourcePos
introducedPosition = newPos "<introduced>" 0 0

introduced :: t -> Located t
introduced = At (Location introducedPosition introducedPosition)


data PredFN ty = PredFN Id [ty] (Maybe ty) Flag
                 deriving (Eq, Show, Typeable, Data)

data Pred ty = Pred Id [ty] Flag deriving (Eq, Typeable, Data)


data Flag = Holds | Fails
          deriving (Eq, Show, Typeable, Data)

data Ctor tyid p t = Ctor { ctorName       :: Located Id
                          , ctorParams     :: [tyid]
                          , ctorQualifiers :: [Located p]
                          , ctorFields     :: [Located t] }
            deriving (Eq, Show, Typeable, Data)

data Fundep t = [t] :~> [t]
            deriving (Eq, Show, Typeable, Data)

determines :: Eq t => Fundep t -> t -> Bool
(xs :~> ys) `determines` z = z `notElem` xs && z `elem` ys

determined :: Eq t => [Fundep t] -> [t] -> [t]
determined fds xs0 = loop xs0
    where loop xs | all (`elem` xs) xs' = xs'
                  | otherwise           = loop xs'
              where xs' = foldl apply xs fds
                    apply xs' (xs :~> ys) | all (`elem` xs') xs = filter (`notElem` xs') ys ++ xs'
                                          | otherwise           = xs'

--

class Binder t
    where bound :: t -> [Id]

withoutBound :: Binder t => t -> [Id] -> [Id]
withoutBound t = filter (`notElem` vs)
    where vs = bound t

instance Binder t => Binder [t]
    where bound = concatMap bound

instance Binder t => Binder (Maybe t)
    where bound = maybe [] bound

instance Binder t => Binder (Located t)
    where bound (At _ t) = bound t

--

class HasVariables t
    where freeVariables :: t -> [Id]
          rename        :: [(Id, Id)] -> t -> t

instance HasVariables t => HasVariables [t]
    where freeVariables = concatMap freeVariables
          rename m = fmap (rename m)

instance HasVariables t => HasVariables (Maybe t)
    where freeVariables = maybe [] freeVariables
          rename m = fmap (rename m)

instance HasVariables t => HasVariables (Located t)
    where freeVariables (At _ t) = freeVariables t
          rename m = fmap (rename m)

--

class Convertable t u
    where convert :: t -> u

instance Convertable t u => Convertable (Maybe t) (Maybe u)
    where convert Nothing  = Nothing
          convert (Just t) = Just (convert t)

instance Convertable t u => Convertable [t] [u]
    where convert = map convert
