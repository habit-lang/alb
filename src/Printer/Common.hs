{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, TypeSynonymInstances #-}
module Printer.Common (module Printer.Common, module Data.Semigroup, SimpleDoc, displayS, displayIO, Fixity(..)) where

import Prelude hiding ((<$>),(<>))

import Control.Monad.Reader
import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import GHC.Exts
import Printer.WadlerLeijen (SimpleDoc, displayS, displayIO)
import qualified Printer.WadlerLeijen as WL
import Syntax.Common
import Syntax.Surface (Assoc(..), dislocate, Fixity(..), Fixities(..), Id, Located(..), mergeFixities)
import Data.Semigroup (Semigroup, (<>))
-- Following Iavor's lead, basically wrapping the pretty-printing library of my choice (in this
-- case, the Wadler-Leijen "prettier printer") in a reader monad to capture details like the current
-- precedence, display options, etc.

newtype Printer t = Printer { runPrinter :: Reader PrinterOptions t }
    deriving (Functor, Applicative, Monad, MonadReader PrinterOptions)

data NameMapping = NM { varNameCounts   :: Map String Int
                      , varNameMap      :: Map Id String
                      , tyvarNameCounts :: Map String Int
                      , tyvarNameMap    :: Map Id String }

data PrinterOptions = PO { precedence     :: Int
                         , showKinds      :: Bool
                         , symbolInfix    :: Bool
                         , fixities       :: Fixities
                         , nameMapping    :: Maybe NameMapping }

defaultOptions = PO { precedence = 0
                    , showKinds = False
                    , symbolInfix = False
                    , fixities = Fixities Map.empty Map.empty
                    , nameMapping = Nothing }

type Doc = Printer WL.Doc

-- The prettier printer
instance Semigroup Doc where
    p1 <> p2        = liftM2 (WL.<>) p1 p2
p1 <+> p2       = liftM2 (WL.<+>) p1 p2
p1 </> p2       = liftM2 (WL.</>) p1 p2
p1 <//> p2      = liftM2 (WL.<//>) p1 p2
p1 <$> p2       = liftM2 (WL.<$>) p1 p2
p1 <$$> p2      = liftM2 (WL.<$$>) p1 p2

infixr 5 </>, <//>, <$>, <$$>
infixr 6 <+>

p1 <::> p2      = p1 <+> text "::" <+> p2
infixr 6 <::>

list, tupled, semiBraces, commaBraces :: [Doc] -> Doc
list            = liftM WL.list . sequence
tupled          = liftM WL.tupled . sequence
semiBraces      = liftM WL.semiBraces . sequence
commaBraces     = liftM WL.commaBraces . sequence

punctuate :: Doc -> [Doc] -> [Doc]
punctuate p []     = []
punctuate p [d]    = [d]
punctuate p (d:ds) = (d <> p) : (punctuate p ds)


group            :: Doc -> Doc
group            = liftM WL.group

sep, fillSep, hsep, vsep :: [Doc] -> Doc
sep             = liftM WL.sep . sequence
fillSep         = liftM WL.fillSep . sequence
hsep            = liftM WL.hsep . sequence
vsep            = liftM WL.vsep . sequence

cat, fillCat, hcat, vcat :: [Doc] -> Doc
cat             = liftM WL.cat . sequence
fillCat         = liftM WL.fillCat . sequence
hcat            = liftM WL.hcat . sequence
vcat            = liftM WL.vcat . sequence

vcatOr :: String -> [Doc] -> Doc
vcatOr s        = liftM (WL.vcatOr s) . sequence

softline, softbreak :: Doc
softline        = return WL.softline
softbreak       = return WL.softbreak

squotes, dquotes, braces, parens, angles, brackets :: Doc -> Doc
squotes         = liftM WL.squotes
dquotes         = liftM WL.dquotes
braces          = liftM WL.braces
parens          = liftM WL.parens
angles          = liftM WL.angles
brackets        = liftM WL.brackets

lparen, rparen, langle, rangle, lbrace, rbrace, lbracket, rbracket :: Doc
lparen          = return WL.lparen
rparen          = return WL.rparen
langle          = return WL.langle
rangle          = return WL.rangle
lbrace          = return WL.lbrace
rbrace          = return WL.rbrace
lbracket        = return WL.lbracket
rbracket        = return WL.rbracket

squote, dquote, semi, colon, comma, space, dot, backslash, equals :: Doc
squote          = return WL.squote
dquote          = return WL.dquote
semi            = return WL.semi
colon           = return WL.colon
comma           = return WL.comma
space           = return WL.space
dot             = return WL.dot
slash           = char '/'
backslash       = return WL.backslash
equals          = return WL.equals
bar             = char '|'

string :: String -> Doc
string          = return . WL.string

bool :: Bool -> Doc
bool            = return . WL.bool

int :: Int -> Doc
int             = return . WL.int

integer :: Integer -> Doc
integer         = return . WL.integer

float :: Float -> Doc
float           = return . WL.float

double :: Double -> Doc
double          = return . WL.double

rational :: Rational -> Doc
rational        = return . WL.rational

indent, hang, nest :: Int -> Doc -> Doc
indent i        = liftM (WL.indent i)
hang i          = liftM (WL.hang i)
nest i          = liftM (WL.nest i)

align :: Doc -> Doc
align           = liftM WL.align

empty :: Doc
empty           = return WL.empty

char :: Char -> Doc
char            = return . WL.char

text :: String -> Doc
text            = return . WL.string

line, linebreak :: Doc
line            = return WL.line
linebreak       = return WL.linebreak

lineOr :: String -> Doc
lineOr s        = return (WL.lineOr s)

-- New combinators

withPrecedence :: Int -> Doc -> Doc
withPrecedence n d = local (\po -> po { precedence = n }) d

atPrecedence :: Int -> Doc -> Doc
atPrecedence n d =
    do prec <- asks precedence
       if prec <= n then withPrecedence n d else parens (withPrecedence n d)

withShowKinds    :: Bool -> Doc -> Doc
withShowKinds b d = local (\po -> po { showKinds = b }) d

withShortenedNames :: Bool -> Doc -> Doc
withShortenedNames True  = local (\po -> po { nameMapping = Just (NM Map.empty Map.empty Map.empty Map.empty) })
withShortenedNames False = local (\po -> po { nameMapping = Nothing })

asInfixSymbol :: Doc -> Doc
asInfixSymbol = local (\po -> po{ symbolInfix = True })

unInfix :: Doc -> Doc
unInfix = local (\po -> po{ symbolInfix = False })

printInfix :: (Printable t, Printable u, Printable v) => Fixity -> t -> u -> v -> Doc
printInfix (Fixity LeftAssoc level) lhs op rhs =
    atPrecedence level (group (align (ppr lhs <+> asInfixSymbol (ppr op) <$> withPrecedence (level + 1) (ppr rhs))))
printInfix (Fixity RightAssoc level) lhs op rhs =
    atPrecedence level (group (align (withPrecedence (level + 1) (ppr lhs) <+> asInfixSymbol (ppr op) <$> ppr rhs)))
printInfix (Fixity NoAssoc level) lhs op rhs =
    atPrecedence level (group (align (withPrecedence (level + 1) (ppr lhs) <+> asInfixSymbol (ppr op) <$> withPrecedence (level + 1) (ppr rhs))))

-- access using: asks showKinds :: Printer Bool


valFixity, typeFixity :: Id -> Printer Fixity
valFixity id = asks (maybe (Fixity LeftAssoc 9) dislocate . Map.lookup id . valFixities . fixities)
typeFixity id = asks (maybe (Fixity LeftAssoc 9) dislocate . Map.lookup id . typeFixities . fixities)
eitherFixity id = do fs <- asks fixities
                     case (Map.lookup id (valFixities fs), Map.lookup id (typeFixities fs)) of
                       (Just f, _) -> return (dislocate f)
                       (Nothing, Just f) -> return (dislocate f)
                       (Nothing, Nothing) -> return (Fixity LeftAssoc 9)

withFixities :: Fixities -> Printer t -> Printer t
withFixities f d = local (\po -> po { fixities = mergeFixities f (fixities po) }) d

lookupVariableName :: (NameMapping -> Map Id String) -> Id -> Printer String
lookupVariableName theMap v =
    do mm <- asks nameMapping
       case mm of
         Nothing -> return (fromId v)
         Just nm -> case Map.lookup v (theMap nm) of
                      Just s  -> return s
                      Nothing -> return (fromId v) -- This shouldn't happen
varName :: Id -> Doc
varName v = lookupVariableName varNameMap v >>= ppr . toId

tyvarName :: Kinded Id -> Doc
tyvarName (Kinded v k) = do v' <- toId `fmap` lookupVariableName tyvarNameMap v
                            ppr (Kinded v' k)

evvarName :: Id -> Doc
evvarName v = lookupVariableName varNameMap v >>= ppr . toId

bindingVariableName :: (NameMapping -> (Map String Int, Map Id String)) ->
                       (Map String Int -> Map Id String -> NameMapping -> NameMapping) ->
                       Id -> (Id -> Doc) -> Doc
bindingVariableName proj inj v@(Ident name _ _) dc =
    do mm <- asks nameMapping
       case mm of
         Nothing -> dc (fromString (fromId v))
         Just nm ->
             case Map.lookup v map of
               Just id -> dc (fromString id)
               Nothing ->
                   case Map.lookup name counts of
                     Nothing -> -- First occurrence of this name
                                local (\po -> po { nameMapping = Just (inj (Map.insert name 1 counts) (Map.insert v name map) nm) })
                                      (dc (fromString name))
                     Just n  -> -- Have been n occurrences already
                                local (\po -> po { nameMapping = Just (inj (Map.insert name (n + 1) counts) (Map.insert v (name ++ '$' : show n) map) nm) })
                                      (dc (fromString (name ++ '$' : show n)))
             where (counts, map) = proj nm

bindingVar :: Id -> (Id -> Doc) -> Doc
bindingVar = bindingVariableName (\nm -> (varNameCounts nm, varNameMap nm)) (\counts map nm -> nm { varNameCounts = counts, varNameMap = map })

bindingTyVar :: Kinded Id -> (Kinded Id -> Doc) -> Doc
bindingTyVar (Kinded v k) dc = bindingVariableName
                                 (\nm -> (tyvarNameCounts nm, tyvarNameMap nm))
                                 (\counts map nm -> nm { tyvarNameCounts = counts, tyvarNameMap = map })
                                 v (\d -> dc (Kinded d k))

bindingEvVar :: Id -> (Id -> Doc) -> Doc
bindingEvVar = bindingVariableName (\nm -> (tyvarNameCounts nm, tyvarNameMap nm)) (\counts map nm -> nm { tyvarNameCounts = counts, tyvarNameMap = map })

-- Rendering

data Renderer = Compact | Pretty Float Int

render :: PrinterOptions -> Renderer -> Doc -> SimpleDoc
render options Compact d          = WL.renderCompact (runReader (runPrinter d) options)
render options (Pretty rfrac w) d = WL.renderPretty rfrac w (runReader (runPrinter d) options)

instance Show Doc
    where showsPrec _ d = displayS (render defaultOptions (Pretty 0.8 100) d)

quoted :: Printable t => t -> String
quoted = show . squotes . ppr

-- Overloading

class Printable t
    where ppr :: t -> Doc

-- Common instances

instance Printable t => Printable (Located t)
    where ppr (At _ t) = ppr t

pprBits val size = "bits<" <> integer val <> "," <> int size <> ">"
                   -- Seems to break in GHC 6.4.2: text ("B" ++ padding ++ toBits val log2)
    where log2 = floor (log (fromIntegral val) / log 2)
          padding = replicate (size - log2 - 1) '0'
          toBits 0 0 = "0"
          toBits 1 0 = "1"
          toBits n k | n >= 2 ^ k = '1' : toBits (n - 2 ^ k) (k - 1)
                     | otherwise = '0' : toBits n (k - 1)

instance Printable Literal
    where ppr (Numeric i) = integer i
          ppr (BitVector val size) = pprBits val size

instance Printable Kind
    where ppr (KVar id) = ppr id
          ppr KStar = char '*'
          ppr KNat = text "nat"
          ppr KArea = text "area"
          ppr KLabel = text "label"
          ppr (KFun lhs rhs) = atPrecedence 0 (withPrecedence 1 (ppr lhs) <+> text "->" <+> ppr rhs)

instance Printable t => Printable (KScheme t)
    where ppr (ForallK [] t)  = ppr t
          ppr (ForallK ids t) = text "forall" <+> cat (punctuate space (map ppr ids)) <> dot <+> ppr t

symbol s@(c:_)
    | s == "()"                                 = text s
    | not (isAlpha c || isNumber c || c == '$') = parens (text s)
    | otherwise                                 = text s

infixSymbol s@(c:_)
    | s == "()"                           = text s
    | isAlpha c || isNumber c || c == '$' = text "`" <> text s <> text "`"
    | otherwise                           = text s

instance Printable Id
    where ppr i = do b <- asks symbolInfix
                     if b then infixSymbol (fromId i) else symbol (fromId i)

instance Printable t => Printable (Kinded t)
    where ppr (Kinded id k) = do b <- asks showKinds
                                 if b then parens (ppr id <+> text "::" <+> ppr k)
                                      else ppr id

instance Printable Doc
    where ppr = id

instance Printable [Char]
    where ppr = text

instance Printable Int
    where ppr = int

instance Printable id => Printable (Fundep id)
    where ppr (xs :~> ys) = hsep (map ppr xs) <+> "->" <+> hsep (map ppr ys)

pprFundep :: Fundep Int -> [Doc] -> Doc
pprFundep (xs :~> []) vs = hsep (map (vs !!) xs) <+> "->"
pprFundep ([] :~> ys) vs = "->" <+> hsep (map (vs !!) ys)
pprFundep (xs :~> ys) vs = hsep (map (vs !!) xs) <+> "->" <+> hsep (map (vs !!) ys)

pprList ts = cat (punctuate (comma <> space) (map ppr ts))
pprList' ts = fillCat (punctuate (comma <> space) (map ppr ts))

instance Printable Flag
    where ppr Holds = empty
          ppr Fails = space <> text "fails"

instance IsString Doc
    where fromString = text
