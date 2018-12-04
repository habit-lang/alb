{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, OverloadedStrings #-}
module Printer.LC (module Printer.LC, Printable(..)) where

-- This file began as a copy of Printer.LambdaCase

import Data.Bits
import Data.Char (isAlpha)
import Printer.Common
import Syntax.Common
import Syntax.LC
import qualified Syntax.LambdaCase as SC
import qualified Printer.LambdaCase as PC

import Prelude hiding ((<$>))

instance Printable Type
    where ppr (TyCon (Kinded id _)) = ppr id
          ppr (TyApp (TyApp (TyCon (Kinded (Ident (s@(c:_)) _ _) _)) d) r)
           | not (isAlpha c)        = atPrecedence 5 (withPrecedence 6 (ppr d) <+> text s <+> ppr r)
          ppr (TyApp (TyApp (TyCon (Kinded (Ident "BitdataCase" _ _) _)) ty) (TyLabel l))
                                    = atPrecedence 10 (ppr ty) <> dot <> ppr l
          ppr (TyApp t t')          = atPrecedence 9 (ppr t <+> withPrecedence 10 (ppr t'))
          ppr (TyLit i)             = integer i
          ppr (TyLabel l)           = dquotes (ppr l)

----------------------------------------------------------------------------------------------------

--instance Printable Expr
--    where ppr (WrappedExpr e) = PC.ppr e

printBitVector :: Integer -> Int -> Doc
printBitVector n s
    | s `mod` 4 == 0 = text "X" <> iter 4 hexDigits (s `div` 4) n
    | s `mod` 3 == 0 = text "O" <> iter 3 octDigits (s `div` 3) n
    | otherwise      = text "B" <> iter 1 binDigits s n
    where hexDigits = "0123456789ABCDEF"
          octDigits = "01234567"
          binDigits = "01"

          -- iter step digits s n prints the bottom 's' digits of 'n', using the list of digits in
          -- 'digits' and stepping by 'step' bits.
          iter step digits 0 _ = empty
          iter step digits s n = iter step digits (s - 1) (n `shiftR` step) <> (char (digits !! (fromIntegral n .&. (2 ^ step - 1))))


instance Printable Expr
    where ppr (EVar id ty)      = ppr id
          ppr (EBits n s)       = printBitVector n s
          ppr (ENat n)          = integer n
          ppr (ECon id ts ty)   = atPrecedence 9 $
                                  ppr id {- <> commaBraces (map ppr ts) -}
          ppr (EBitCon id [])   = ppr id
          ppr (EBitCon id es)   = ppr id <> brackets (cat (punctuate (comma <> space) [ppr f <+> equals <+> ppr e | (f, e) <- es]))
          ppr (ELam id ty body) = atPrecedence 9 $
                                  ((backslash <+>
                                   parens
                                   (text (fromId id) <+>
                                    text "::" <+> ppr ty) <+>
                                   text "->") <+> (nest 3 $ ppr body))
          ppr (ELet ds body)    = atPrecedence 9
                                . align
                                $ text "let" <+> align (ppr ds) </> text "in" <+> (align (ppr body))
          ppr (ECase e alts)    = atPrecedence 9
                                $ align
                                $ ((text "case" <+> withPrecedence 9 (ppr e) <+> text "of") <$$>
                                   indent 2 (align . vcat $ map ppr alts))
          ppr (EApp e e')       = parens $ atPrecedence 9 (ppr e <+> (withPrecedence 10 (ppr e')))
          ppr (EBitSelect e f)  = atPrecedence 10 (ppr e) <> dot <> ppr f
          ppr (EBitUpdate e f e') = atPrecedence 10 (ppr e) <> brackets (ppr f <+> equals <+> ppr e')
          ppr e@(EFatbar e1 e2) = parens $ ppr e1 <+> bar <+> ppr e2
          ppr (EBind "_" _ e body)
                                = align ((align (ppr e) <> semi) <$$> ppr body)
          ppr (EBind var varty e body)
                                = align ((ppr var {- <+> text "::" <+> ppr varty -} <+> text "<-" <+> align (ppr e) <> semi) <$$> ppr body)
          ppr (EDo e)           = text "do" <+> ppr e
          ppr (EReturn e)       = atPrecedence 9 (text "primRet" <+> withPrecedence 10 (ppr e))

instance Printable Alt
    where ppr (Alt c [] [] e)   = ppr c <+> text "->" <+> align (ppr e)
          ppr (Alt c tys ids e) = ppr c {- <> (commaBraces (map (withPrecedence 0 . ppr) tys)) -}
                              <+> hsep (map ppr ids)
                              <+> text "->" <+> (align (ppr e))

instance Printable Defn
    where ppr (Defn i t (Left (pi,ts))) = text "external" <+> ppr i <+> braces (hsep (ppr pi : map (atPrecedence 10 . ppr) ts))<+> text "::" <+> ppr t
          ppr (Defn i@(Ident s _ _) t (Right e)) = align (ppr i <+> text "::" <+> ppr t Printer.Common.<$>
                                                         ppr i <+> text "=" <+> (withPrecedence 0 $ ppr e))

instance Printable Decl
    where ppr (Decl dn) = ppr dn

instance Printable Decls
    where ppr (Decls ds) = align (vcat (map ppr ds))

instance Printable TopDecl
    where ppr (Datatype name params ctors) = nest 4 (text "data" <+> ppr name <+> cat (punctuate space (map (atPrecedence 10 . ppr) params)) <+> pprCtors)
              where pprCtor (name, fields) = ppr name <+> sep (map (atPrecedence 10 . ppr) fields)
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]

          ppr (Bitdatatype name size ctors) = nest 4 (text "bitdata" <+> ppr name <> text "/" <> int size <+> pprCtors)
              where pprCtor (name, fields) = ppr name <+> brackets (align (cat (punctuate (space <> bar <> space) (map ppr fields))))
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> align (pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ])

          ppr (Struct name size fields) =
              nest 4 (ppr name <> int size <+> brackets (cat (punctuate (softline <> bar <> space) (map ppr fields))) )

          ppr (Area name v init ty size align) =
              nest 4 ((if v then text "volatile" <> space else empty) <>
                      text "area" <+> (ppr name <+> text "<-" <+> ppr init) </> text "::" <+> ppr ty <+> sizeAlign size align)

sizeAlign size align = text ("{- size = "++show size++", align = "++show align++" -}")

instance Printable BitdataField
    where ppr (LabeledField name ty width offset) =
              ppr name <::> ppr ty <+> widthOffset width offset
          ppr (ConstantField v width offset) = integer v <+> widthOffset width offset

widthOffset width offset = text ("{- width = "++show width++", offset = "++show offset++" -}")

instance Printable StructField
    where ppr (StructField mname ty width offset)
            = maybe id (\name -> (ppr name <::>)) mname (ppr ty <+> widthOffset width offset)

instance Printable Entrypoints
    where ppr (Entrypoints []) = empty
          ppr (Entrypoints is) = text "entrypoint" <+> hcat (punctuate comma (map (ppr . fst) is))

instance Printable Program
    where ppr p = vcat (punctuate line ([text "type M = Proc"] ++
                                        [ppr notMainEntries] ++
                                        (if null mainEntries
                                         then []
                                         else ["hmain = unsafeRunProc" <+> ppr (fst (head mainEntries)) <$>
                                               "entrypoint hmain"]) ++
                                        map ppr (topDecls p)  ++
                                        [ppr (decls p)]))
              where mainEntries = filter snd (fromEntrypoints (entrypoints p))
                    notMainEntries = Entrypoints (filter (not . snd) (fromEntrypoints (entrypoints p)))
