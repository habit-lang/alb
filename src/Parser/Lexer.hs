{-# OPTIONS_GHC -fno-warn-name-shadowing -XFlexibleContexts #-}
module Parser.Lexer where

import Control.Monad.Identity
import Data.Char
import Data.List
import Syntax.Common (Id, fromString)
import Text.Parsec.Prim
import Text.Parsec.Char
import Text.Parsec.Combinator hiding (lookAhead)
import Text.Parsec.Error (errorPos, setErrorPos)
import Text.Parsec.Indentation
import Text.Parsec.Indentation.Char
import Text.Parsec.Indentation.Token
import Text.Parsec.Pos
import qualified Text.Parsec.Token as T

import Debug.Trace (trace)

-----------------------------------------------------------
-- Language definition
-----------------------------------------------------------

languageDef :: T.GenLanguageDef String () Identity
languageDef  = T.LanguageDef {
                 T.caseSensitive  = True
               , T.commentStart   = "{-"
               , T.commentEnd     = "-}"
               , T.commentLine    = "--"
               , T.nestedComments = True
               , T.identStart     = letter
               , T.identLetter   = alphaNum <|> oneOf "_'"
               , T.opStart       = T.opLetter languageDef
               , T.opLetter      = oneOf ":!#$%&*+./<=>?@\\^|-~"
               , T.reservedNames = [ "area", "aligned", "bitdata","case", "class"
                                   , "data", "deriving", "do", "else"
                                   , "extends", "exists", "fails", "forall", "if", "in"
                                   , "infix", "infixl", "infixr"
                                   , "instance", "let", "of", "struct"
                                   , "then", "type", "where"
                                   , "opaque", "primitive", "requires", "volatile", "require" ]
               , T.reservedOpNames = [".","..","::","=","\\","|", "->"
                                     , "<-", "=>", "~", "`"] }


lexer :: T.GenTokenParser (IndentStream (CharIndentStream String)) () Identity
lexer = makeTokenParser (makeIndentLanguageDef languageDef)

reserved       = T.reserved lexer
reservedOp     = T.reservedOp lexer
charLiteral    = T.charLiteral lexer
stringLiteral  = T.stringLiteral lexer
natural        = T.natural lexer
integer        = T.integer lexer
float          = T.float lexer
naturalOrFloat = T.naturalOrFloat lexer
symbol         = T.symbol lexer
lexeme         = T.lexeme lexer
whiteSpace     = T.whiteSpace lexer
parens         = T.parens lexer
braces         = T.braces lexer
brackets       = T.brackets lexer
semi           = T.semi lexer
comma          = T.comma lexer
colon          = T.colon lexer
dot            = T.dot lexer
semiSep        = T.semiSep lexer
sepiSep1       = T.semiSep1 lexer
commaSep       = T.commaSep lexer
commaSep1      = T.commaSep1 lexer

type ParseM = Parsec (IndentStream (CharIndentStream String)) ()
nullState = ()

identifier :: (Char -> Bool) -> ParseM Id
identifier pred =
    try (do (c:cs) <- T.identifier lexer
            guard (pred c)
            return (fromString (c:cs)))

operator :: (Char -> Bool) -> ParseM Id
operator pred =
    try (do (c:cs) <- T.operator lexer
            guard (pred c)
            return (fromString (c:cs)))

middle :: String -> ParseM ()
middle s = localIndentation Any (reserved s)

ticks = between (symbol "`") (symbol "`")

sign           :: Num a => ParseM (a -> a)
sign            =   (char '-' >> return negate)
                <|> (char '+' >> return id)
                <|> return id

number_ :: Integer -> ParseM Char -> ParseM (Integer, Int)
number_ base baseDigit =
    do digits <- concat `fmap` (optional (char '_') >> many1 baseDigit `sepBy1` char '_')
       let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
       seq n (return (n, length digits))

number :: Integer -> ParseM Char -> ParseM Integer
number base baseDigit = fst `fmap` number_ base baseDigit

decimal, hexadecimal, octal, binary :: ParseM Integer
decimal         = number 10 digit
hexadecimal     = number 16 hexDigit
octal           = number 8 octDigit
binary          = number 2 (oneOf "01")

dotSep1 p = sepBy1 p dot

spaceSep1 p = sepBy1 p whiteSpace

layout p = T.braces lexer (T.semiSep1 lexer p) <|>
           localIndentation Gt (concat `fmap` many (absoluteIndentation (T.semiSep1 lexer p)))
