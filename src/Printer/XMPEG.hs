{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Printer.XMPEG (module Printer.XMPEG, Printable(..), quoted) where

-- This file is mostly copy-pasted from Printer.IMPEG, although as I continue to work on the XMPEG
-- tree they may diverge further.  This does raise the question about whether some commonality could
-- be extracted from both syntax trees.  At the moment I'm not optimistic; although many of the
-- constructors are similar/the same, the differences don't seem to fit any particular patterns.

import Prelude hiding ((<$>))

import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Printer.Common
import Syntax.Common
import Syntax.XMPEG
import qualified Utils.BDD as BDD

instance Printable Type
    where ppr (TyCon id)   = ppr id
          ppr (TyVar id)   = tyvarName id
          ppr (TyGen i)    = text "_" <> int i
          ppr t@(TyApp _ _) =
              case getFixity' op of
                Just f | length args == 2 -> printInfix f lhs op rhs
                    where [lhs, rhs] = args
                _ -> hang 4 (group (atPrecedence 9 (vsep (map (withPrecedence 10 . ppr) (op : args)))))
              where (op, args) = flattenType t
                    getFixity' (TyVar (Kinded id _)) = getFixity id
                    getFixity' (TyCon (Kinded id _)) = getFixity id
                    getFixity' _                     = Nothing
          ppr (TyNat i)    = integer i
          ppr (TyLabel l)  = dquotes (ppr l)

instance Printable (Pred Type)
    where ppr (Pred cl args f) = ppr cl <+> cat (punctuate space (map (withPrecedence 10 . ppr) args)) <> ppr f

instance Printable t => Printable (Scheme t)
    where ppr (Forall ks es t) = align (group (vsep [ group ( vcat [ braces (align (fillSep (punctuate comma [text "_" <> int i <::> ppr k | (i, Kinded _ k) <- zip [0..] ks ])))
                                                                   , braces (cat (punctuate (comma <> space) (map ppr es))) ])
                                                    , align (ppr t) ]))

----------------------------------------------------------------------------------------------------

instance Printable Expr
    where ppr (ELamVar id)      = varName id
          ppr (ELetVar inst)    = ppr inst
          ppr (EBits value size) = pprBits value size
          ppr (ECon inst)       = ppr inst
          ppr (EBitCon id fields) = ppr id <> brackets (cat (punctuate (comma <> space) [ppr name <+> equals <+> ppr value | (name, value) <- fields]))
          ppr e@(ELam _ _ _)    = iter paramNames []
              where (params, body) = flattenLambda e
                    (paramNames, paramTypes) = unzip params
                    iter [] ds     = group (atPrecedence 0 (hang 4 (backslash <+> hsep [parens (ppr v <::> ppr ty) | (v, ty) <- zip (reverse ds) paramTypes] <+> "->" <$> ppr body)))
                    iter (p:ps) ds = bindingVar p (\d -> iter ps (d:ds))
          ppr (EMethod d n ts evs) = ppr d <> dot <> int n <> pprTypeArgs ts evs
          ppr (ELet ds body) = iter (bound ds) (align (atPrecedence 0 (text "let" <+> align (ppr ds) </> text "in" <+> ppr body)))
              where iter [] d     = d
                    iter (v:vs) d = bindingVar v (const (iter vs d))
          ppr (ELetTypes (Left cs) body) = align (atPrecedence 0 ("let types" <+> align pprCases </> text "in" <+> ppr body))
              where pprCases = cat (punctuate (semi <> softline) [pprPairs cond <+> "->" <+> pprPairs impr | (cond, impr) <- cs])
                    pprPairs ps = brackets (cat (punctuate (comma <> space) [ppr t <> slash <> tyvarName v | (v, t) <- ps]))
          ppr (ELetTypes (Right (args, results, _)) body) =
              iter results $
              atPrecedence 0 (group (align ("let types" <+> braces (hsep (punctuate comma (map tyvarName results))) <+> equals <+> "computed" <> braces (hsep (punctuate comma (map tyvarName args))) <$>
                                            "in" <+> ppr body)))
              where iter [] d = d
                    iter (v:vs) d = bindingTyVar v (const (iter vs d))
          ppr (ESubst exprSubst evSubst body) =
              hang 4 (pprSubst exprSubst </> pprSubst evSubst </> ppr body)
          ppr (EMatch m)        = braces (align (withPrecedence 0 (ppr m)))
          ppr e@(EApp _ _)      =
              case getFixity' op of
                Just f | length args == 2 -> printInfix f lhs op rhs
                    where [lhs, rhs] = args
                _ -> hang 4 (group (atPrecedence 9 (vsep (map (withPrecedence 10 . ppr) (op : args)))))
              where (op, args) = flattenApp e
                    getFixity' (ELamVar id)            = getFixity id
                    getFixity' (ELetVar (Inst id _ _)) = getFixity id
                    getFixity' (ECon (Inst id _ _))    = getFixity id
                    getFixity' _                       = Nothing
          ppr (EBitSelect e f) = withPrecedence 10 (ppr e) <> dot <> ppr f
          ppr (EBitUpdate e f e') = ppr e <> brackets (ppr f <+> equals <+> ppr e')
          ppr (EStructInit c es) = ppr c <> brackets (cat (punctuate (comma <> space) [ppr f <+> "<-" <+> ppr e | (f, e) <- es]))
          ppr e@(EBind {}) =
              iter binds $
              atPrecedence 0 ("do" <+> align (vcat pprBinds <$> ppr result))
              where (binds, result) = flattenDo e
                    pprBinds = [ hang 4 (group (vsep [ varName v <+> group ("<-" <> align (group (vcat [ braces (ppr ta <> comma <> ppr tb <> comma <> ppr tm)
                                                                                                   , braces (ppr me) ])))
                                                      , ppr e <> semi ]))
                                 | (ta, tb, tm, me, v, e) <- binds ]
                    iter [] d                   = d
                    iter ((_,_,_,_,v,_) : bs) d = bindingVar v (const (iter bs d))

          ppr (EReturn e) = atPrecedence 9 ("return" <+> withPrecedence 10 (ppr e))

pprSubst subst = brackets (cat (punctuate (comma <> softline) [ppr e <+> slash <+> ppr v | (v, e) <- subst]))

instance Printable Ev
    where ppr (EvVar id) = evvarName id
          ppr (EvCons (Inst id ts args)) =
              cat (punctuate softline (ppr id <> braces (cat (punctuate (comma <> softline) (map ppr ts))) : map (withPrecedence 10 . ppr) args))
          ppr (EvRequired id es) = hang 4 (atPrecedence 9 (cat (punctuate softline ("required" : ppr id : map (withPrecedence 10 . ppr) es))))
          ppr (EvCases cs) = "cases" <+> braces (align (cat (punctuate (semi <> softline) [pprPairs cond <+> "->" <+>
                                                                                           ppr ev | (cond, ev) <- cs])))
              where pprPairs ps = brackets (cat (punctuate (comma <> space) [ppr t <> slash <> ppr v | (v, t) <- ps]))
          ppr (EvComputed ts _) = "computed" <> braces (cat (punctuate (comma <> space) (map ppr ts)))
          ppr (EvFrom pat ev ev') = parens (ppr pat <+> "<-" <+> ppr ev) <+> "=>" <+> ppr ev'

instance Printable EvPat
    where ppr (EvPat id ts pvars) = ppr id <> braces (cat (punctuate (comma <> space) (map ppr ts))) <> parens (cat (punctuate (comma <> space) (map ppr pvars)))
          ppr (EvWild)            = "_"

instance Printable ([EvPat], Ev)
    where ppr (pats, ev) = parens (cat (punctuate (comma <> space) (map ppr pats))) <+> "->" <+> ppr ev

instance Printable Inst
    where ppr (Inst id [] []) = varName id -- special case to reduce noise :-)
          ppr (Inst id ts es) = varName id <> unInfix (group (pprTypeArgs ts es))

pprTypeArgs      :: [Type] -> [Ev] -> Doc
pprTypeArgs ts es = align (group (vcat [withPrecedence 0 (braceList ts), group (withPrecedence 0 (braceList es))]))

braceList xs      = braces (align (cat (punctuate (comma <> line) (map ppr xs))))

----------------------------------------------------------------------------------------------------

instance Printable Pattern
    where ppr PWild                 = text "_"
          ppr (PVar id ty)          = atPrecedence 9 (varName id <::> ppr ty)
          ppr (PCon inst vs)        = atPrecedence 9 (group (hang 4 (vsep [ ppr inst
                                                                          , hsep (map varName vs)])))

----------------------------------------------------------------------------------------------------

instance Printable Match
    where ppr MFail          = text "fail"
          ppr (MCommit e)    = text "^" <> atPrecedence 10 (ppr e)
          ppr m@(MElse _ _)  = group (parens (vsep ((space <> nest 2 (ppr m')) : ["|" <+> nest 2 (ppr m'') | m'' <- ms]) <> space))
              where (m':ms) = flattenElses m
          ppr m@(MGuarded _ _) = atPrecedence 0 $
                                 iter (concatMap bound guards)
                                      (group (nest 4 ((align (vsep [ ppr g <+> "=>" | g <- guards])) <$> ppr result)))
              where (guards, result) = flattenGuards m
                    iter [] d        = d
                    iter (v:vs) d    = bindingVar v (const (iter vs d))

instance Printable Guard
    where ppr (GLet ds)   = hang 4 (text "let" <+> ppr ds)
          ppr (GFrom p e) = hang 4 (ppr p <+> text "<-" </> ppr e)
          ppr (GSubst evs) = pprSubst evs
          ppr (GLetTypes (Left cs)) = hang 4 ("let types" <+> align pprCases)
              where pprCases = cat (punctuate (semi <> softline) [pprPairs cond <+> "->" <+> pprPairs impr | (cond, impr) <- cs])
                    pprPairs ps = brackets (cat (punctuate (comma <> space) [ppr t <> slash <> tyvarName v | (v, t) <- ps]))
          ppr (GLetTypes (Right (args, results, _))) =
              atPrecedence 0 ("let types" <+> braces (hsep (punctuate comma (map ppr results))) <+> equals <+> "computed" <> braces (hsep (punctuate comma (map ppr args))))


instance Printable Decls
    where ppr (Decls defns) = vcat (punctuate line (map ppr defns))

printAbstraction :: Printable t => Id -> Gen t -> Doc
printAbstraction name (Gen typarams evparams body) =
    tyiter typarams $ eviter evparams $
    hang 4 (group (vsep [group (varName name <> align (vcat [ braces (fillSep (punctuate comma (map tyvarName typarams)))
                                                            , braces (fillSep (punctuate comma (map evvarName evparams))) ]))

                        , equals <+> ppr body]))
    where tyiter [] d         = d
          tyiter (tp : tps) d = bindingTyVar tp (const (tyiter tps d))
          eviter [] d         = d
          eviter (ep : eps) d = bindingEvVar ep (const (eviter eps d))

instance Printable Defn
    where ppr (Defn name scheme (Right abs)) =
               align (varName name <::> ppr scheme <$> printAbstraction name abs)
          ppr (Defn name scheme (Left (impl, types))) =
               "primitive" <+> ppr name <+> (align ((":: " <> ppr scheme) <$> equals <+> text impl <> params types))
            where params ps = braces (cat (punctuate (comma <> space) (map ppr ps)))

----------------------------------------------------------------------------------------------------

instance Printable typaram => Printable (TopDecls typaram)
    where ppr tops = vcat (punctuate line (map ppr tops))

instance Printable typaram => Printable (TopDecl typaram)
    where ppr (Datatype name params ctors) = nest 4 (text "data" <+> ppr name <+> cat (punctuate space (map (atPrecedence 10 . ppr) params)) <> pprCtors)
              where pprCtor (name, ks, ps, fields) = hang 4 (ppr name </>
                                                             sep (map (atPrecedence 10 . ppr) fields) </>
                                                             (if null ks then empty else text "forall" <+> cat (punctuate (comma <> space) (map ppr ks))) </>
                                                             (if null ps then empty else (text "if" <+> cat (punctuate (comma <> space) (map ppr ps)))))
                    pprCtors =
                        case ctors of
                          [] -> empty
                          (first : rest) -> space <> equals </> pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ]

          ppr (Bitdatatype name pat ctors) = nest 4 (text "bitdata" <+> ppr name <+> slash <+> int (BDD.width pat)
                                                     </> coverage pat </> pprCtors)
              where pprCtor (name, [], pat)     = ppr name <+> coverage pat
                    pprCtor (name, fields, pat) = ppr name <+> brackets (align (cat (punctuate (space <> bar <> space)
                                                                                               (map ppr fields)))) <+> coverage pat
                    pprCtors =
                        case ctors of
                          []             -> empty
                          (first : rest) -> space <> equals <+> align (pprCtor first <> cat [ softline <> bar <+> pprCtor ctor | ctor <- rest ])

          ppr (Struct name size fields) =
              hang 4 (text "struct" <+> ppr name <+> slash <+> int size <+> brackets (cat (punctuate (softline <> bar <> space) (map ppr fields))))

          ppr (Area v ids ty size align) =
              hang 4 ((if v then text "volatile " else empty) <>
                      text "area" <+> cat (punctuate (comma <> softline) [ ppr name <+> text "<-" <+> ppr init | (name, init) <- ids ])
                                  </> text "::" <+> ppr ty
                                  <+> sizeAlign size align)

sizeAlign size align = text ("{- size = "++show size++", align = "++show align++" -}")

coverage pat = text "{- coverage: " <+> ppr pat <+> text "-}"

instance Printable BitdataField
    where ppr (LabeledField name ty pat offset) = ppr name <::> ppr ty <+> patOffset pat offset
          ppr (ConstantField v pat offset)      = integer v <+> patOffset pat offset

patOffset pat offset = widthOffset (BDD.width pat) offset <+> coverage pat

widthOffset width offset = text ("{- width = "++show width++", offset = "++show offset++" -}")

instance Printable StructField
    where ppr (StructField mname ty width offset)
            = maybe id (\name -> (ppr name <::>)) mname ( ppr ty <+> widthOffset width offset)

----------------------------------------------------------------------------------------------------

instance Printable t => Printable (Gen t)
    where ppr (Gen typarams evparams impl) =
              braces (params typarams) <+> braces (params evparams)
              <+> text "->"
              <+> ppr impl
              where params xs = cat (punctuate (comma <> space) (map ppr xs))

instance Printable [Gen Inst]
    where ppr methods = parens (brackets (align (cat (punctuate (comma <> space) (map ppr methods)))))

----------------------------------------------------------------------------------------------------

instance Printable typaram => Printable (Program typaram)
    where ppr p = iter (bound (decls p)) $
                  vcat (punctuate line (map ppr (topDecls p) ++
                                        [ppr (decls p)] ++
                                        map pprEvDecl (Map.assocs (evidence p))))

                  where iter [] d         = d
                        iter (v:vs) d     = bindingVar v (const (iter vs d))

                        pprEvDecl (name, (evtype, dict)) =
                            ppr name <::> ppr evtype <$>
                            printAbstraction name dict
