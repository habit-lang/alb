module PrettyMPEG(showM, prettyM,
                  showP, prettyP,
                  showE, prettyE,
                  showG, prettyG,
                  ppDecls) where

import MPEG

import Char
import Text.PrettyPrint

-----------------------------------------------------------------------
-- Simple AST to String conversion for MPEG:

showM Fail        = "fail"
showM (Commit e)  = "^" ++ showEp e
showM (m :||:  n) = showMp m ++ " | " ++ showM n
showM (g :=>: m)  = showG g ++ " => " ++ showMp m

showMp m
  = case m of
      Fail       -> showM m
      Commit _   -> showM m
      (m :||: n) -> showMp m ++ " | " ++ showMp n
      (_ :=>: _) -> "(" ++ showM m ++ ")"

-- patterns:

showP (Var i) = i
showP (CPat c ps) = c ++ loop ps
 where loop [] = []
       loop (p:ps) = " " ++ showPp p ++ loop ps
showP (Guard p g)  = showP p ++ " | " ++ showG g

showPp p
  = case p of
      Var i     -> i
      CPat c [] -> c
      _         -> "(" ++ showP p ++ ")"

-- expressions:

showE (Id i)       = i
showE (Cons c es)  = c ++ loop es
 where loop [] = []
       loop (e:es)  = " " ++ showEp e ++ loop es
showE (Ap (Ap (Id f) x) y)
     | isAlpha (head f) = f ++ " " ++ showEp x ++ " " ++ showEp y
     | otherwise        = showEp x ++ " " ++ f ++ " " ++ showEp y
showE (Ap f x)      = showE f ++ " " ++ showEp x
showE (Lam i e)     = "\\" ++ i ++ " -> " ++ showE e
showE (LamStr i e)  = "\\*" ++ i ++ " -> " ++ showE e
showE (LamAmp i e)  = "\\&" ++ i ++ " -> " ++ showE e
showE (Match m)     = "{ " ++ showM m ++ " }"
showE (LetE i e e') = "let " ++ i ++ " = " ++ showE e ++ " in " ++ showE e'
showE (Bind i e e') = i ++ " <- " ++ showE e ++ "; " ++ showE e'

showEp e
  = case e of
     Id i      -> i
     Cons c [] -> c
     Match _   -> showE e
     _         -> "(" ++ showE e ++ ")"

-- guards:

showG (Let i e) = "let " ++ i ++ " = " ++ showE e
showG(From p e) = showPp p ++ " <- " ++ showE e

-----------------------------------------------------------------------
-- Simple pretty printer for MPEG:

prettyM Fail        = text "fail"
prettyM (Commit e)  = text "^" <> prettyEp e
prettyM (m :||:  n) = prettyMp m $$ (text "|" <+> prettyM n)
prettyM (g :=>: m)  = (prettyG g <+> text "=>") $$ nest 2 (prettyMp m)

prettyMp m
  = case m of
      Fail       -> prettyM m
      Commit _   -> prettyM m
      (m :||: n) -> prettyMp m $$ (text "|" <+> prettyMp n)
      (_ :=>: _) -> parens (prettyM m)

-- patterns:

prettyP (Var i) = text i
prettyP (CPat c ps) = text c <+> loop ps
 where loop [] = empty
       loop (p:ps) = prettyPp p <+> loop ps
prettyP (Guard p g)  = prettyP p <+> text "|" <+> prettyG g

prettyPp p
  = case p of
      Var i     -> text i
      CPat c [] -> text c
      _         -> parens (prettyP p)

-- expressions:

prettyE (Id i)        = text i
prettyE (Cons c es)   = text c <+> loop es
 where loop [] = empty
       loop (e:es)   = prettyEp e <+> loop es
prettyE (Ap (Ap (Id f) x) y)
     | isAlpha (head f) = text f <+> prettyEp x <+> prettyEp y
     | otherwise        = prettyEp x <+> text f <+> prettyEp y
prettyE (Ap f x)      = prettyE f <+> prettyEp x
prettyE (Lam i e)     = text "\\" <> text i <+> text "->" <+> prettyE e
prettyE (LamStr i e)     = text "\\*" <> text i <+> text "->" <+> prettyE e
prettyE (LamAmp i e)     = text "\\&" <> text i <+> text "->" <+> prettyE e
prettyE (Match m)     = braces (prettyM m)
prettyE (LetE i e e') = (text "let" <+> text i <+> text "=" <+> prettyE e)
                        $$ (text "in" <+> prettyE e')
prettyE (Bind i e e') = (text i <+> text "<-" <+> prettyE e <> semi)
                        $$ prettyE e'

prettyEp e
  = case e of
     Id i      -> text i
     Cons c [] -> text c
     Match _   -> prettyE e
     _         -> parens (prettyE e)

-- guards:

prettyG (Let i e) = text "let" <+> text i <+> text "=" <+> prettyE e
prettyG(From p e) = prettyPp p <+> text "<-" <+> prettyEp e

-----------------------------------------------------------------------
-- Pretty printing utilities:

ppDecls = render . vcat . map prettyG

-----------------------------------------------------------------------
