{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, UndecidableInstances #-}
module Printer.IMPEG (module Printer.IMPEG, Printable(..), quoted) where

import Prelude hiding ((<$>))

import Control.Monad.Reader
import Data.List ((\\), isPrefixOf)
import Data.Maybe (isJust)
import Printer.Common hiding (tyvarName, bindingTyVar)
import qualified Printer.Common as Common
import Syntax.IMPEG hiding (paramName)
import Syntax.IMPEG.TSubst hiding (empty)

----------------------------------------------------------------------------------------------------

class (Printable t, Ord t) => TyId t
    where isTupleCon   :: t -> Maybe Int
          isProxyCon   :: t -> Bool
          tyvarName    :: t -> Doc
          bindingTyVar :: t -> (t -> Doc) -> Doc
          tyvarFixity  :: t -> Maybe Fixity

instance TyId Id
    where isTupleCon (Ident id 0 _)
              | "$Tuple" `isPrefixOf` id = Just (read (drop 6 id))
          isTupleCon _                   = Nothing

          isProxyCon (Ident s 0 _) = s == "Proxy"
          isProxyCon _             = False

          tyvarName = evvarName -- type and evidence variables share the same namespace
          bindingTyVar = bindingEvVar
          tyvarFixity = getFixity

instance TyId KId
    where isTupleCon (Kinded id _)  = isTupleCon id
          isProxyCon (Kinded id _)  = isProxyCon id
          tyvarName                 = Common.tyvarName
          bindingTyVar              = Common.bindingTyVar
          tyvarFixity (Kinded id _) = getFixity id

instance TyId (Either KId Id)
    where isTupleCon   = either isTupleCon isTupleCon
          isProxyCon   = either isProxyCon isProxyCon
          tyvarName    = either tyvarName tyvarName
          bindingTyVar (Left kid) dc = bindingTyVar kid (dc . Left)
          bindingTyVar (Right id) dc = bindingTyVar id (dc . Right)
          tyvarFixity  = either tyvarFixity tyvarFixity


class TyId t => TyParam t
    where paramName :: t -> Id

instance TyParam (Either KId Id)
    where paramName (Left (Kinded name _)) = name
          paramName (Right name)           = name

instance TyParam KId
    where paramName (Kinded name _) = name

instance TyId t => Printable (Type t)
    where ppr (TyCon id) =
              case isTupleCon id of
                Just n -> parens (cat (replicate n comma))
                Nothing -> ppr id
          ppr (TyVar id)     = tyvarName id
          ppr (TyGen i)      = text "_" <> int i
          ppr (TyApp (At _ (TyCon id)) t)
              | isProxyCon id = "#" <> atPrecedence 10 (ppr t)
          ppr t@(TyApp t0 t1) =
              case (op, getFixity' op) of
                (At _ (TyCon s), _)
                    | isJust (isTupleCon s) -> parens (align (fillSep (punctuate comma (map ppr args))))
                (_, Just f)
                    | length args == 2 -> printInfix f lhs op rhs
                    where [lhs, rhs] = args
                _ -> hang 4 (group (atPrecedence 9 (vsep (map (withPrecedence 10 . ppr) (op : args)))))
              where (op, args) = flattenType (introduced t)
                    getFixity' (At _ (TyVar id)) = tyvarFixity id
                    getFixity' (At _ (TyCon id)) = tyvarFixity id
                    getFixity' _                 = Nothing
          ppr (TyNat l)      = integer l
          ppr (TyKinded t k) = atPrecedence 0 (withPrecedence 1 (ppr t) <::> ppr k)
          ppr (TyLabel l)    = dquotes (ppr l)

instance Printable (Either (Kinded Id) Id)
    where ppr (Left kinded) = ppr kinded
          ppr (Right v)     = ppr v

instance TyId t => Printable (PredType PredFN t)
    where ppr (PredFN name args Nothing flag) =
              ppr name <+> atPrecedence 10 (hsep (map ppr args)) <> ppr flag
          ppr (PredFN name args (Just arg) flag) =
              ppr name <+> atPrecedence 10 (hsep (map ppr args)) <+> equals <+> ppr arg <> ppr flag

instance TyId t => Printable (PredType Pred t)
    where ppr (Pred name args flag) =
              hang 4 (ppr name <+> atPrecedence 10 (fillSep (map ppr args)) <> ppr flag)

instance (Printable p, Printable t) => Printable (Qual p t)
    where ppr ([] :=> t)  = ppr t
          ppr ([p] :=> t) = group (hang 4 (ppr p <+> text "=>" <$> ppr t))
          ppr (ps :=> t)  = group (hang 4 (parens (align (fillSep (punctuate comma (map ppr ps)))) <+> text "=>" <$> ppr t))

instance (TyId tyid, Printable (Type tyid), Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Scheme p tyid)
    where ppr (Forall [] qt) = ppr qt
          ppr (Forall ps qt) = iter ps []
              where iter (v:vs) xs = bindingTyVar v (\x -> iter vs (x:xs))
                    iter [] xs     = do b <- asks showKinds
                                        group (hang 4 (if b then header <$> ppr qt' else ppr qt'))
                        where xs' = reverse xs
                              qt' = inst (map TyVar xs') qt
                              header = text "forall" <+> align (fillSep (map ppr xs')) <> dot

----------------------------------------------------------------------------------------------------

instance (TyId tyid, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Expr p tyid)
    where ppr (ELet ds body)                 = iter (bound ds) $
                                               atPrecedence 0 (group (align (text "let" <+> align (ppr ds) <$> "in" <+> ppr body)))
              where iter (v:vs) d = bindingVar v (const (iter vs d))
                    iter []     d = d
          ppr e@(ELam _ _)                   = iter params []
              where (params, body) = flattenLambda e
                    iter [] vs     = group (atPrecedence 0 (hang 4 (backslash <> hsep (map ppr (reverse vs)) <+> "->" <$> ppr body)))
                    iter (p:ps) vs = bindingVar p (\v -> iter ps (v:vs))
          ppr e@(ELamStr _ _)                   = iter params []
              where (params, body) = flattenLambda e
                    iter [] vs     = group (atPrecedence 0 (hang 4 (backslash <> "*" <+> hsep (map ppr (reverse vs)) <+> "->" <$> ppr body)))
                    iter (p:ps) vs = bindingVar p (\v -> iter ps (v:vs))
          ppr e@(ELamAmp _ _)                   = iter params []
              where (params, body) = flattenLambda e
                    iter [] vs     = group (atPrecedence 0 (hang 4 (backslash <> "&" <+> hsep (map ppr (reverse vs)) <+> "->" <$> ppr body)))
                    iter (p:ps) vs = bindingVar p (\v -> iter ps (v:vs))
          ppr (EVar id)                      = varName id
          ppr (ECon id)                      =
              case isTupleCon id of
                Just n  -> parens (cat (replicate n comma))
                Nothing -> ppr id
          ppr (EBitCon id ps)                = ppr id <> brackets (cat (punctuate (space <> bar <> space) [ppr v <+> equals <+> ppr e | (v, e) <- ps]))
          ppr (EBits value size)             = pprBits value size
          ppr (EMatch m)                     = braces (align (withPrecedence 0 (ppr m)))
          ppr e@(EApp _ _) =
              case (op, getFixity' op) of
                (At _ (ECon c), _)
                    | isJust (isTupleCon c) -> parens (cat (punctuate comma (map ppr args)))
                (op, Just f)
                    | length args == 2 ->
                        printInfix f lhs op rhs
                    where [lhs, rhs] = args
                _ -> hang 4 (group (atPrecedence 9 (vsep (map (atPrecedence 10 . ppr) (op : args)))))
              where (op, args) = flattenApp (introduced e)
                    getFixity' (At _ (EVar id)) = getFixity id
                    getFixity' (At _ (ECon id)) = getFixity id
                    getFixity' _                = Nothing
          ppr e@(EBind {}) = iter binds $ atPrecedence 0 ("do" <+> align (vcatOr "; " (pprBinds ++ [ppr result])))
              where (binds, result)     = flattenDo e
                    pprBinds            = [ hang 4 (varName v <+> "<-" <+> ppr e) | (v, e) <- binds ]
                    iter [] d           = d
                    iter ((v,_) : bs) d = bindingVar v (const (iter bs d))

          ppr (EStructInit name fields)      = ppr name <> brackets (cat (punctuate (space <> bar <> space) [ ppr id <+> text "<-" <+> ppr e | (At _ id, e) <- fields ]))

instance (TyId tyid, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Pattern p tyid)
    where ppr PWild                      = text "_"
          ppr (PVar id)                  = varName id
          ppr (PCon id ps)
              | isJust (isTupleCon id)   = parens (cat (punctuate comma (map varName ps)))
              | otherwise                =
                  case (getFixity id, ps) of
                    (Just f, [lhs, rhs]) -> printInfix f (varName lhs) id (varName rhs)
                    _                    -> atPrecedence 9 (cat (punctuate space (ppr id : map varName ps)))
          ppr (PTyped p t)               = atPrecedence 0 (withPrecedence 1 (ppr p)) <::> ppr t
          ppr (PGuarded p g)             = atPrecedence 1 (withPrecedence 2 (ppr p) <+> bar <+> ppr g)

instance (TyId tyid, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Match p tyid)
    where ppr MFail          = text "fail"
          ppr (MCommit e)    = text "^" <> withPrecedence 10 (ppr e)
          ppr m@(MElse _ _)  = group (parens (vsep ((space <> nest 2 (ppr m')) : ["|" <+> nest 2 (ppr m'') | m'' <- ms]) <> space))
              where (m': ms) = flattenElses m
          ppr m@(MGuarded _ _) = atPrecedence 0 $
                                 iter (concatMap bound guards)
                                      (group (nest 4 ((align (vsep [ ppr g <+> "=>" | g <- guards])) <$> ppr result)))
              where (guards, result) = flattenGuards m
                    iter [] d        = d
                    iter (v:vs) d    = bindingVar v (const (iter vs d))

instance (TyId tyid, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Guard p tyid)
    where ppr (GLet ds)   = hang 4 (text "let" <+> ppr ds)
          ppr (GFrom p e) = atPrecedence 1 (withPrecedence 2 (ppr p) <+> text "<-" <+> ppr e)

instance (TyId tyid, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Decls p tyid)
    where ppr (Decls groups) = vcatOr "; " (punctuate line (map ppr groups))

instance (TyId tyid, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Signature p tyid)
    where ppr (Signature id ty) = varName id <::> align (ppr ty)

pprFunction (name, [], body) = group (hang 4 (varName name <+> equals <$> braces (align (ppr body))))
pprFunction (name, params, body) = iter params $ group (hang 4 (varName name <+> cat (punctuate space (map varName params)) <+> equals <$> braces (align (ppr body))))
    where iter [] d     = d
          iter (v:vs) d = bindingVar v (const (iter vs d))

instance (TyId tyid, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (TypingGroup p tyid)
    where ppr (Pattern p m signatures) =
              align (vcatOr "; " (map ppr signatures ++ [ppr p <+> equals <+> braces (align (ppr m))]))
          ppr (Explicit (name, params, body) tys) =
              align (vcatOr "; " [ varName name <::> ppr tys, pprFunction (name, params, body) ])
          ppr (Implicit fcns) =
              align (vcatOr "; " (punctuate line (map pprFunction fcns)))
          ppr (PrimValue s name) = hang 4 (text "primitive" <+> ppr s <$> equals <+> text name)

----------------------------------------------------------------------------------------------------

instance (TyId tyid, TyParam typaram, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (TopDecl p tyid typaram)
    where ppr (Class name params constraints methods defaults) =
              iter (map dislocate params) $
              nest 4 (text "class" <+> ppr name <+> cat (punctuate space (map ppr params))
                      <> pprConstraints <> pprMethods)
              where iter [] d     = d
                    iter (v:vs) d = bindingTyVar v (const (iter vs d))
                    pprConstraints | null constraints = empty
                                   | otherwise        = space <> bar <+> cat (punctuate (comma <> space) (map pprConstraint constraints))
                    pprMethods     | null methods     = empty
                                   | otherwise        = line <> nest 6 (text "where" <+> vcat (map ppr methods ++ map pprFunction defaults))
                    paramNames = map (ppr . paramName . dislocate) params
                    pprConstraint (At _ (Fundep fd)) = pprFundep fd paramNames
                    pprConstraint (At _ (Opaque i))  = "opaque" <+> (paramNames !! i)

          ppr (Instance name _ ((hypotheses :=> conclusion, methods) : alternatives)) =
              text "instance" <+> pprInstanceBody 0 conclusion hypotheses methods <> (if null alternatives then empty else line <> pprAlts)
              where pprInstanceBody n conclusion hypotheses methods =
                        nest 4 (group (clauseName n <::> ppr conclusion <$>
                                       if null hypotheses then empty else text "if" <+> nest 3 (fillSep (punctuate "," (map ppr hypotheses)))) <> pprMethods)
                        where pprMethods | null methods = empty
                                         | otherwise = line <> indent 4 (hang 6 (text "where" <+> vcat (map pprFunction methods)))
                    pprAlts = vcat [ text "else" <+> pprInstanceBody n conclusion hypotheses decls | (n, (hypotheses :=> conclusion, decls)) <- zip [1..] alternatives ]
                    clauseName 0 | null alternatives = ppr name
                    clauseName n = ppr name <> "_" <> int n

          ppr (Require ps qs) =
              "require" <+> cat (punctuate ", " (map (ppr . snd) ps)) <+> "if" <+> cat (punctuate ", " (map ppr qs))

          ppr (Datatype name params ctors drv) = nest 4 (text "data" <+> ppr name <+> cat (punctuate space (map ppr params)) <+> pprCtors <> pprDrvs)
              where pprCtor (Ctor name quant preds fields sh) = ppr name <+> align (sep (map (atPrecedence 10 . ppr) fields) <> pprQuant <> pprPreds) <+> ppr (show sh)
                        where pprQuant | null quant = empty
                                       | otherwise  = softline <> text "forall" <+> align (cat (punctuate (comma <> softline) (map ppr quant)))
                              pprPreds | null preds = empty
                                       | otherwise  = softline <> text "if" <+> align (cat (punctuate (comma <> softline) (map ppr preds)))
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]
                    pprDrvs | null drv = empty
                            | otherwise = softline <> text "deriving" <+> parens (cat (punctuate comma (map ppr drv)))

          ppr (Bitdatatype name size ctors drv) = nest 4 (text "bitdata" <+> ppr name <> (maybe empty (\t -> slash <> ppr t) size) <+> pprCtors <> pprDrvs)
              where pprCtor (Ctor name quant preds fields sh) = ppr name
                      <+> brackets (cat (punctuate (space <> bar <> space) (map ppr fields))) <> pprQuant <> pprPreds <+> ppr (show sh)
                        where pprQuant | null quant = empty
                                       | otherwise  = space <> text "forall" <+> cat (punctuate (comma <> space) (map ppr quant))
                              pprPreds | null preds = empty
                                       | otherwise  = space <> text "if" <+> cat (punctuate (comma <> space) (map ppr preds))
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> equals <+> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]
                    pprDrvs | null drv = empty
                            | otherwise = softline <> text "deriving" <+> parens (cat (punctuate comma (map ppr drv)))

          ppr (Struct name size (Ctor _ ks ps regions sh) drv) =
              nest 4 (text "struct" <+>
                      ppr name <>
                      maybe empty (\t -> slash <> ppr t) size <+>
                      brackets (cat (punctuate (softline <> bar <> space) (map ppr regions))) <>
                      pprQuant <> pprPreds <> pprDrvs) <+> ppr (show sh)
              where pprQuant | null ks = empty
                             | otherwise = softline <> text "forall" <+> cat (punctuate (comma <> space) (map ppr ks))
                    pprPreds | null ps = empty
                             | otherwise = softline <> text "if" <+> cat (punctuate (comma <> softline) (map ppr ps))
                    pprDrvs  | null drv = empty
                             | otherwise = softline <> text "deriving" <+> parens (cat (punctuate comma (map ppr drv)))


          ppr (Area v ids ty) =
              nest 4 ((if v then text "volatile " else empty) <>
                      text "area" <+> cat (punctuate (comma <> softline) [ ppr name <+> text "<-" <+> ppr init | (name, init) <- ids ])
                               </> text "::" <+> ppr ty)

instance TyId tyid => Printable (BitdataField tyid)
    where ppr (LabeledField name ty init) =
              ppr name <> maybe empty (\init -> space <> equals <+> ppr init) init <::> ppr ty
          ppr (ConstantField e) = ppr e

instance TyId tyid => Printable (StructRegion tyid)
    where ppr (StructRegion Nothing ty) = ppr ty
          ppr (StructRegion (Just (StructField id Nothing)) ty) = ppr id <::> ppr ty
          ppr (StructRegion (Just (StructField id (Just init))) ty) = ppr id <+> text "<-" <+> ppr init <::> ppr ty

instance (TyId tyid, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Primitive p tyid)
    where ppr (PrimCon (Signature name tys) impl) = text "primitive" <+> ppr name <::> ppr tys <+> equals <+> ppr impl
          ppr (PrimType name k) = text "primitive" <+> text "type" <+> ppr name <::> ppr k
          ppr (PrimClass name params constraints methods) =
              nest 4 (text "primitive" <+> text "class" <+> ppr name <+> cat (punctuate space (map ppr params))
                      <> pprConstraints <> pprMethods)
              where pprConstraints | null constraints = empty
                                   | otherwise        = space <> bar <+> cat (punctuate (comma <> space) (map ppr constraints))
                    pprMethods     | null methods     = empty
                                   | otherwise        = line <> nest 6 (text "where" <+> vcat (map ppr methods))

----------------------------------------------------------------------------------------------------

instance (TyId tyid, TyParam typaram, Printable (PredType p tyid), HasTypeVariables (PredType p tyid) tyid) => Printable (Program p tyid typaram)
    where ppr p = vcat (punctuate line (map ppr (topDecls p) ++
                                        [ppr (decls p)]))
