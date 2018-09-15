{-# LANGUAGE TypeSynonymInstances #-} -- For Printable Id instance
module Printer.Surface (module Printer.Surface, Printable(..), quoted) where

import Prelude hiding ((<$>))

import Data.Char
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Printer.Common hiding (printInfix)
import Syntax.Surface as Surface

-- this is probably wrong
isOperator (Ident s@(c:_) 0 _) = s /= "()" && not (isAlphaNum c) && c /= '_'
isOperator _                   = False

printInfix :: Printable t => (Id -> Printer Fixity) -> Id -> t -> t -> Doc
printInfix fixity id@(Ident op 0 _) lhs rhs =
    do f <- fixity id
       case f of
         Fixity NoAssoc n    -> atPrecedence n (withPrecedence (n + 1) (ppr lhs) <+> text op <+> withPrecedence (n + 1) (ppr rhs))
         Fixity LeftAssoc n  -> atPrecedence n (ppr lhs <+> text op <+> withPrecedence (n + 1) (ppr rhs))
         Fixity RightAssoc n -> atPrecedence n (withPrecedence (n + 1) (ppr lhs) <+> text op <+> ppr rhs)
printInfix _ id lhs rhs = pprApp (pprApp (ppr id) (ppr lhs)) (ppr rhs)
    where pprApp x y = atPrecedence 9 (x <+> withPrecedence 10 y)

instance Printable Type
    where ppr (TyCon s) = ppr s
          ppr (TyVar s) = ppr s
          ppr TyWild = text "_"
          ppr (TyApp (At _ (TyApp (At _ (TyVar op)) lhs)) rhs)
              | isOperator op = printInfix typeFixity op lhs rhs
          ppr (TyApp (At _ (TyApp (At _ (TyVar op)) lhs)) rhs)
              | isOperator op = printInfix typeFixity op lhs rhs
          ppr (TyApp t t') = atPrecedence 9 (ppr t <+> withPrecedence 10 (ppr t'))
          ppr (TyNat i) = integer i
          ppr (TyTuple ts) = parens (cat (punctuate comma (map ppr ts)))
          ppr (TyTupleCon n) = parens (cat (replicate n comma))
          ppr (TyKinded t k) = ppr t <+> text "::" <+> ppr k
          ppr (TyLabel s) = char '#' <> ppr s
          ppr (TySelect t (At _ l)) = withPrecedence 10 (ppr t) <> dot <> ppr l
          ppr (TyInfix first rest) = atPrecedence 8 (withPrecedence 9 (ppr first <+> hsep [ ppr op <+> ppr t | (op, t) <- rest ]))

instance Printable Pred
    where ppr (Pred (At _ t) mt Holds) =
              ppr t <> maybe empty (\t -> space <> equals <+> ppr t) mt
          ppr (Pred (At _ t) mt Fails) =
              ppr t <> maybe empty (\t -> space <> equals <+> ppr t) mt <+> text "fails"

instance Printable t => Printable (Qual t)
    where ppr ([] :=> t) = ppr t
          ppr (preds :=> t) = parens (cat (punctuate comma (map ppr preds))) <+> text "=>" <+> ppr t

instance Printable Expr
    where ppr (ELet ds body) = text "let" <+> ppr ds </> text "in" <+> ppr body
          ppr (EIf cond cons alt) = text "if" <+> ppr cond </> text "then" <+> ppr cons </> text "else" <+> ppr alt
          ppr (ECase scrutinee alts) = nest 4 (text "case" <+> ppr scrutinee <+> text "of" <$> align (vcat (map ppr alts)))
          ppr (ELam patterns body) = nest 4 (backslash <> withPrecedence 10 (hsep (map ppr patterns)) <+> text "->" </> ppr body)
          ppr (EVar id) = ppr id
          ppr (ECon id) = ppr id
          ppr (ELit l) = ppr l
          ppr (ETuple es) = parens (cat (punctuate comma (map ppr es)))
          ppr (ETupleCon n) = parens (cat (replicate n comma))
          ppr (EApp (At _ (EApp (At _ (EVar op)) lhs)) rhs)
              | isOperator op = printInfix valFixity op lhs rhs
          ppr (EApp (At _ (EApp (At _ (EVar op)) lhs)) rhs)
              | isOperator op = printInfix valFixity op lhs rhs
          ppr (EApp e e') = atPrecedence 9 (ppr e <+> withPrecedence 10 (ppr e'))
          ppr (EBind Nothing e rest) = ppr e <> semi </> ppr rest
          ppr (EBind (Just var) e rest) = ppr var <+> text "<-" <+> ppr e <> semi </> ppr rest
          ppr (ESelect e (At _ l)) = withPrecedence 10 (ppr e) <> dot <> ppr l
          ppr (EUpdate e fields) = ppr e <+> brackets (align (cat (punctuate (space <> bar <> space) [ ppr id <+> equals <+> ppr val | (id, val) <- fields ])))
          ppr (ELeftSection e (At _ op)) = parens (ppr e <+> ppr op)
          ppr (ERightSection (At _ op) e) = parens (ppr op <+> ppr e)
          ppr (EStructInit name fields) = ppr name <+> brackets (align (cat (punctuate (space <> bar <> space) [ ppr id <+> equals <+> ppr val | (id, val) <- fields ])))
          ppr (ETyped expr ty) = atPrecedence 0 (withPrecedence 1 (ppr expr)) <::> ppr ty
          ppr (EInfix first rest) = atPrecedence 8 (withPrecedence 9 (ppr first <+> hsep [ ppr op <+> ppr e | (op, e) <- rest ]))

instance Printable Scrutinee
    where ppr (ScExpr e) = ppr e
          ppr (ScFrom Nothing e) = text "<-" <+> ppr e
          ppr (ScFrom (Just id) e) = ppr id <+> text "<-" <+> ppr e

instance Printable Pattern
    where ppr (PVar id) = ppr id
          ppr (PLit l) = ppr l
          ppr PWild = char '_'
          ppr (PAs id p) = atPrecedence 0 (ppr id <+> char '@' <+> withPrecedence 1 (ppr p))
          ppr (PTyped p t) = atPrecedence 0 (withPrecedence 1 (ppr p) <+> text "::" <+> ppr t)
          ppr (PCon id) = ppr id
          ppr (PTuple ps) = parens (cat (punctuate comma (map ppr ps)))
          ppr (PTupleCon n) = parens (cat (replicate n comma))
          ppr (PApp (At _ (PApp (At _ (PCon op)) lhs)) rhs)
              | isOperator op = printInfix eitherFixity op lhs rhs
          ppr (PApp (At _ (PApp (At _ (PVar op)) lhs)) rhs)
              | isOperator op = printInfix eitherFixity op lhs rhs
          ppr (PApp p p') = atPrecedence 9 (ppr p <+> withPrecedence 10 (ppr p'))
          ppr (PLabeled name fields) = ppr name <+> brackets (align (cat (punctuate (space <> bar <> space) (map ppr fields))))
          ppr (PInfix first rest) = atPrecedence 8 (withPrecedence 9 (ppr first <+> hsep [ ppr op <+> ppr e | (op, e) <- rest ]))

instance Printable FieldPattern
    where ppr (FieldPattern id p) = ppr id <+> equals <+> ppr p

printMaybeDecls :: Maybe Decls -> Doc
printMaybeDecls Nothing = empty
printMaybeDecls (Just ds) = line <> nest 6 (text "where" <+> ppr ds)

printRhs :: String -> Rhs -> Doc
printRhs separator (Unguarded body ds) = text separator <+> ppr body <> printMaybeDecls ds
printRhs separator (Guarded ps ds) = align (vcat [ bar <+> ppr guard <+> text separator <+> ppr body | (guard, body) <- ps ]) <> printMaybeDecls ds

instance Printable Alt
    where ppr (p :-> rhs) = ppr p <+> printRhs "->" rhs

instance Printable Equation
    where ppr (lhs := rhs) = nest 4 (ppr lhs <+> printRhs "=" rhs)

instance Printable Signature
    where ppr (Signature id (ps :=> t)) = ppr id <+> text "::" <> (if null ps then empty else space <> parens (cat (punctuate comma (map ppr ps))) <+> text "=>") <+> ppr t

instance Printable Fixities
    where ppr f = vcat (map printTypeFixity (Map.assocs (typeFixities f)) ++ map printFixity (Map.assocs (valFixities f)))
              where printTypeFixity (id, At _ (Fixity assoc n)) = ppr assoc <+> text "type" <+> int n <+> if isOperator id then ppr id else char '`' <> ppr id <> char '`'
                    printFixity (id, At _ (Fixity assoc n)) = ppr assoc <+> int n <+> if isOperator id then ppr id else char '`' <> ppr id <> char '`'

instance Printable Assoc
    where ppr LeftAssoc = text "infixl"
          ppr RightAssoc = text "infixr"
          ppr NoAssoc = text "infix"

instance Printable Decls
    where ppr ds = withFixities (Surface.fixities ds) (vsep (map ppr (signatures ds) ++ map ppr (equations ds)) <> pprFixities)
              where pprFixities | Map.null (typeFixities (Surface.fixities ds)) && Map.null (valFixities (Surface.fixities ds)) = empty
                                | otherwise = line <> ppr (Surface.fixities ds)

instance Printable Class
    where ppr (Class lhs determined constraints decls) = nest 4 (text "class" <+> ppr lhs <> pprDetermined <> pprCs <> printMaybeDecls decls)
              where pprDetermined =
                        case determined of
                          Nothing -> empty
                          Just t  -> space <> equals <+> ppr t
                    pprCs | null constraints = empty
                          | otherwise = space <> bar <+> cat (punctuate comma (map ppr constraints))

instance Printable ClassConstraint
    where ppr (Superclass p) = ppr p
          ppr (Fundep (xs :~> ys)) = vars xs <+> text "->" <+> vars ys
              where vars = cat . punctuate comma . map ppr
          ppr (Opaque v) = text "opaque" <+> ppr v

instance Printable Instance
    where ppr (Instance ((hypotheses :=> conclusion, decls) : alternatives)) =
              text "instance" <+> pprInstanceBody conclusion hypotheses decls <> pprAlts
              where pprInstanceBody conclusion hypotheses decls =
                        ppr conclusion <+> (if null hypotheses then empty else text "if" <+> cat (punctuate comma (map ppr hypotheses))) <> nest 4 (printMaybeDecls decls)
                    pprAlts | null alternatives = empty
                            | otherwise = vcat [ line <> text "else" <+> pprInstanceBody conclusion hypotheses decls | (hypotheses :=> conclusion, decls) <- alternatives ]

instance Printable Requirement
    where ppr (Require ps qs) = "require" <+> cat (punctuate ", " (map ppr ps)) <+> "if" <+> cat (punctuate ", " (map ppr qs))

instance Printable Synonym
    where ppr (Synonym lhs rhs interface) = (if isJust interface then text "opaque" <> space else empty) <>
                                            text "type" <+> ppr lhs <+> equals <+> ppr rhs <> nest 4 (printMaybeDecls interface)

instance Printable Datatype
    where ppr (Datatype lhs ctors drv interface) = nest 4 ((if isJust interface then text "opaque" <> space else empty) <>
                                                           text "data" <+> ppr lhs <> pprCtors <> pprDrvs <> nest 4 (printMaybeDecls interface))
              where pprCtor (Ctor name _ [] fields) = ppr name <+> pprFields fields
                    pprCtor (Ctor name _ preds fields) = ppr name <+> pprFields fields <+> text "if" <+> cat (punctuate comma (map ppr preds))
                    pprFields fs
                        | all unlabeled fs = sep (map (atPrecedence 10 . pprField) fs)
                        | otherwise        = brackets (cat (punctuate " | " (map pprField fs)))
                        where unlabeled (At _ (DataField Nothing _)) = True
                              unlabeled _                     = False
                              pprField (At _ (DataField (Just l) t)) = ppr l <+> "::" <+> ppr t
                              pprField (At _ (DataField Nothing t))  = ppr t

                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]
                    pprDrvs | null drv = empty
                            | otherwise = softline <> text "deriving" <+> parens (cat (punctuate comma (map ppr drv)))

instance Printable Bitdatatype
    where ppr (Bitdatatype lhs size ctors drv) = nest 4 (text "bitdata" <+> ppr lhs <> (maybe empty (\t -> slash <> ppr t) size) <> pprCtors <> pprDrvs)
              where pprCtor (Ctor name _ [] fields) = ppr name <+> brackets (cat (punctuate (space <> bar <> space) (map ppr fields)))
                    pprCtor (Ctor name _ preds fields) = ppr name <+> brackets (cat (punctuate (space <> bar <> space) (map ppr fields)))  <+> text "if" <+> cat (punctuate comma (map ppr preds))
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]
                    pprDrvs | null drv = empty
                            | otherwise = softline <> text "deriving" <+> parens (cat (punctuate comma (map ppr drv)))

instance Printable BitdataField
    where ppr (LabeledField name ty init) =
              ppr name <> maybe empty (\init -> space <> equals <+> ppr init) init <::> ppr ty
          ppr (ConstantField e) = ppr e

instance Printable Struct
    where ppr (Struct name size (Ctor _ _ preds regions) drv) =
              nest 4 (ppr name <>
                      maybe empty (\t -> slash <> ppr t) size <+>
                      brackets (cat (punctuate (softline <> bar <> space) (map ppr regions))) <>
                      (if null preds then empty else softline <> text "if" <+> cat (punctuate (comma <> softline) (map ppr preds))) <>
                      pprDrvs)
              where pprDrvs | null drv = empty
                            | otherwise = softline <> text "deriving" <+> parens (cat (punctuate comma (map ppr drv)))

instance Printable StructRegion
    where ppr (StructRegion Nothing ty) = ppr ty
          ppr (StructRegion (Just (StructField id Nothing)) ty) = ppr id <+> text "::" <+> ppr ty
          ppr (StructRegion (Just (StructField id (Just init))) ty) = ppr id <+> text "<-" <+> ppr init <+> text "::" <+> ppr ty


instance Printable Area
    where ppr (Area v ids ty decls) =
              nest 4 ((if v then text "volatile " else empty) <>
                      text "area" <+> cat (punctuate (comma <> softline) [ ppr name <> maybe empty (\init -> space <> text "<-" <+> ppr init) init | (name, init) <- ids ])
                               </> text "::" <+> ppr ty <> printMaybeDecls decls)

instance Printable Primitive
    where ppr (PrimValue s name private) = text "primitive" <+> (if private then empty else "private" <> space) <>
                                           ppr s <+> parens (text name)
          ppr (PrimCon s name private) = text "primitive" <+> (if private then empty else "private" <> space) <>
                                         ppr s <+> parens (text name)
          ppr (PrimType t)        = text "primitive" <+> ppr t
          ppr (PrimClass lhs rhs constraints decls) = text "primitive" <+> ppr (Class lhs rhs (map (fmap Fundep) constraints) decls)

instance Printable Program
    where ppr p = vcat (punctuate line (map ppr (datatypes p) ++
                                        map ppr (bitdatatypes p) ++
                                        map ppr (structures p) ++
                                        map ppr (synonyms p) ++
                                        map ppr (classes p) ++
                                        map ppr (instances p) ++
                                        map ppr (areas p) ++
                                        map ppr (primitives p) ++
                                        [ppr (Surface.decls p)]))
