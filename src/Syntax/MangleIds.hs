{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Syntax.MangleIds (mangleProgram, mangleId) where

--------------------------------------------------------------------------------
-- This module mangles variable names to be compatible with the CompCert back-end
--------------------------------------------------------------------------------

import Prelude hiding (pure)

import Data.Char (ord, isAlpha, isDigit)
import Data.Generics

import Common
import Syntax.Common
import Syntax.LC

{-
This mangling scheme is not perfect (i.e., it is not injective) because
names like "<>" and "LtGt" map to the same string.  But this won't be
a problem for names that already have a $uniquenumber suffix, and the
initial upper case letters (which can only be used for Conids in Habit)
should prevent conflicts with the names of user defined functions.

The requirements for name mangling determined by the CompCert back-end.
Thus the result of mangling must match:
  ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '_' '$' '0'-'9']*

A better name mangling schemes would be to use "_" as an escape
character.  For example "$$" becomes "_Dollar_Dollar" and "a_b'"
becomes "a__b_Quote".

We could also use "$" as an escape character, but we would need to
prefix "_" on the front to ensure that we don't start with "$".  For
example, "$$" becomes "_$Dollar$Dollar" and "a_b'" becomes
"a_b$Quote".

NOTE: We do *not* use "fresh" because we want identical names to
mangle to identical names.
-}

mangleId (Ident [] _ _) = error "Internal error: zero length Id"
mangleId id@(Ident (c:cs) n f) =
    Ident (mangleChar True c ++ concatMap (mangleChar False) cs) n f
    where mangleChar                   :: Bool -> Char -> String
          mangleChar _ c | isAlpha c    = [c]
          mangleChar False c | isDigit c= [c]
          mangleChar _ '_'              = "_"
          mangleChar _ ':'              = "Colon"
          mangleChar _ '!'              = "Bang"
          mangleChar _ '#'              = "Hash"
          mangleChar True '$'           = "Dollar"
          mangleChar False '$'          = "$"
          mangleChar _ '%'              = "Percent"
          mangleChar _ '&'              = "Amp"
          mangleChar _ '*'              = "Star"
          mangleChar _ '+'              = "Plus"
          mangleChar _ '.'              = "Dot"
          mangleChar _ '/'              = "Slash"
          mangleChar _ '<'              = "Lt"
          mangleChar _ '='              = "Eq"
          mangleChar _ '>'              = "Gt"
          mangleChar _ '?'              = "Quest"
          mangleChar _ '@'              = "At"
          mangleChar _ '\\'             = "Back"
          mangleChar _ '^'              = "Caret"
          mangleChar _ '|'              = "Pipe"
          mangleChar _ '-'              = "Dash"
          mangleChar _ '~'              = "Tilde"
          mangleChar _ '\''             = "Quote"
          mangleChar _ '"'              = "DQuote"
          mangleChar _ '['              = "LBracket"
          mangleChar _ ']'              = "RBracket"
          mangleChar _ '('              = "LParen"
          mangleChar _ ')'              = "RParen"
          mangleChar _ c                = "Ord"++show (ord c)

mangleType :: Type -> Bool
mangleType (TyCon (Kinded "->" _)) = True
mangleType _                       = False

mangleProgram :: (Typeable t, Data t) => Pass () t t
mangleProgram = pure (everywhereBut (mkQ False mangleType) (mkT mangleId))
