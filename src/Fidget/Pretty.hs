{-# OPTIONS -Wall -fno-warn-orphans #-}

module Fidget.Pretty(pprogram) where

import Fidget.AST
import Syntax.Common (fromId, fromString)
import Text.PrettyPrint.HughesPJ

import Data.Int

data Token = SIMPLEE | ALLOCE | LETE | LETRECE | IFE | CASEE
  | ERRORE | GOTOE | GVARA | VARA | CONSTA | INTCONST | AREACONST | LOADA | INT32
  | RELAXA | MODA | IXLEQA | ATA | SELA | IXUNSIGNEDA | NZUNSIGNED | PTR | UNOPA | BINOPA
  | ATOME | CALLE | MINUS | PLUS |  AMPERSAND | APPE
  | AUDITED | BAR
  | BANGEQUAL | STAR | SLASH | PERCENT | SLASHU | PERCENTU | CARET
  | LESSLESS | GREATERGREATER | GREATERGREATERU | EQUALEQUAL | ARRAYA
  | LESS | LESSEQUAL | GREATER | GREATEREQUAL | EQUALEQUALU | BANGEQUALU
  | LESSU | LESSEQUALU | GREATERU | GREATEREQUALU
  | INT8U | INT8S | INT16U | INT16S | BANG | TILDE
  | TUNIT | TRECORDT
  | TFUNT | TIXT | TREFT | F | IXCASEE | TCONT
  | STOREDA | STRUCTA | REFC | INTC | IXC
  | LETLABELE  | EXTERN | INLINE | INT | FLOAT
  | VOLATILE | NONVOLATILE
  | EXTERNAL | BUILTIN | VLOAD | VSTORE | MEMCPY
  | TNZERO | TPTR

instance Show Program where
   showsPrec _ p = shows (pprogram p)

instance Show Expr where
   showsPrec _ e = shows (pexp e)

instance Show Token where
   showsPrec _ t = shows (tok t)

instance Show Ftyp where
  showsPrec _ ty = shows (pty ty)

instance Show Function where
  showsPrec _ f = shows (pfunct f)

instance Show SimplExpr where
  showsPrec _ se = shows (psimpleexp se)

instance Show Atom where
  showsPrec _ a = shows (patom a)

toks :: Token -> String
toks t = case t of
  ALLOCE -> "alloc"
  AMPERSAND -> "&"
  APPE      -> "app"
  AREACONST -> "area"
  ARRAYA    -> "array"
  ATA       -> "at"
  ATOME     -> "atom"
  AUDITED   -> "audited"
  BANG      -> "!"
  BANGEQUALU -> "!=u"
  BAR       -> "|"
  BANGEQUAL -> "!="
  BINOPA    -> "binop"
  CALLE     -> "call"
  CARET     -> "^"
  CASEE     -> "case"
  CONSTA    -> "const"
  EQUALEQUAL -> "=="
  EQUALEQUALU -> "==u"
  ERRORE      -> "error"
  EXTERN    -> "extern"
  F         -> "funct"
  FLOAT     -> "float"
  GOTOE     -> "goto"
  GREATER   -> ">"
  GREATEREQUAL -> ">="
  GREATEREQUALU -> ">=u"
  GREATERGREATER -> ">>"
  GREATERGREATERU -> ">>u"
  GREATERU      -> ">u"
  IFE       -> "if"
  INLINE    -> "inline"
  INT       -> "int"
  INT8U     -> "int8u"
  INT8S     -> "int8s"
  INT16U    -> "int16u"
  INT16S    -> "int16s"  
  INT32     -> "int32"
  INTC      -> "cint"
  INTCONST  -> "intconst"
  IXC       -> "cix"
  IXCASEE   -> "ixcase"
  IXLEQA    -> "ixleq"
  IXUNSIGNEDA    -> "ixunsigned"
  LESS      -> "<"
  LESSEQUAL -> "<="
  LESSEQUALU -> "<=u"
  LESSLESS   -> "<<"
  LESSU      -> "<u"
  LETE       -> "let"
  LETLABELE  -> "letlabel"
  LETRECE      -> "letrec"
  LOADA        -> "load"
  MINUS        -> "-"
  MODA         -> "modix"
  NONVOLATILE  -> "nonvolatile"
  NZUNSIGNED    -> "nzunsigned"
  SIMPLEE      -> "simple"
  PERCENT      -> "%"
  PERCENTU     -> "%u"
  PLUS         -> "+"
  PTR          -> "ptr"
  REFC         -> "cref"
  RELAXA       -> "relax"
  STOREDA      -> "stored"
  SELA         -> "sel"
  SLASH        -> "/"
  SLASHU       -> "/u"
  STAR         -> "*"
  STRUCTA      -> "struct"
  TCONT        ->  "tc"
  TFUNT        -> "->"
  TILDE        -> "~"
  TIXT         -> "ix"
  TRECORDT     -> "record"
  TREFT        -> "ref"
  TUNIT        -> "unit"
  TNZERO       -> "nzero"
  TPTR         -> "ptr"
  UNOPA        -> "unop"
  VARA         -> "var"
  GVARA         -> "gvar"
  VOLATILE     -> "volatile"

  EXTERNAL     -> "external"
  BUILTIN      -> "builtin"
  VLOAD        -> "vload"
  VSTORE       -> "vstore"
  MEMCPY       -> "memcpy"

tok :: Token -> Doc
tok t = text (toks t)

{-
spaces :: [Doc] -> [Doc]
spaces = intersperse (text " ")
-}

sexp :: Token -> [Doc] -> Doc
sexp t stuff = parens (tok t <+> sep stuff)

slist :: [Doc] -> Doc
slist stuff = parens (sep stuff)

vslist :: [Doc] -> Doc
vslist stuff = parens (vcat stuff)

pmachint :: Int32 -> Doc
pmachint i = integer (fromIntegral i)

pvar :: Id -> Doc
pvar = pid

pid :: Id -> Doc
pid s = text ("\"" ++ fromId s ++ "\"")

pconst :: Constant -> Doc
pconst Ounit              = parens empty
pconst (Ointconst i)      = sexp INTCONST [pmachint i]
pconst (Oarea v a)        = sexp AREACONST [pvar v,parea a]

punop :: Unary_operation -> Doc
punop Ocast8unsigned = tok INT8U
punop Ocast8signed = tok INT8S
punop Ocast16unsigned = tok INT16U
punop Ocast16signed = tok INT16S
punop Onegint = tok MINUS
punop Onotbool = tok BANG
punop Onotint = tok TILDE
punop (Orelax m n) = sexp RELAXA [pmachint m,pmachint n]
punop (Oixunsigned n) = sexp IXUNSIGNEDA [pmachint n]
punop (Omodix n) = sexp MODA [pmachint n]
punop (Onzunsigned) = sexp NZUNSIGNED []
punop (Optr) = sexp PTR []

pbinop :: Binary_operation -> Doc
pbinop Oadd       = tok PLUS
pbinop Osub       = tok MINUS
pbinop Omul       = tok STAR
pbinop Odiv       = tok SLASH
pbinop Omod       = tok PERCENT
pbinop Odivu      = tok SLASHU
pbinop Omodu      = tok PERCENTU
pbinop Oand       = tok AMPERSAND
pbinop Oor        = tok BAR
pbinop Oxor       = tok CARET
pbinop Oshl       = tok LESSLESS
pbinop Oshr       = tok GREATERGREATER
pbinop Oshru      = tok GREATERGREATERU
pbinop (Ocmp Ceq) = tok EQUALEQUAL
pbinop (Ocmp Cne) = tok BANGEQUAL
pbinop (Ocmp Clt) = tok LESS
pbinop (Ocmp Cle) = tok LESSEQUAL
pbinop (Ocmp Cgt) = tok GREATER
pbinop (Ocmp Cge) = tok GREATEREQUAL
pbinop (Ocmpu Ceq) = tok EQUALEQUALU
pbinop (Ocmpu Cne) = tok BANGEQUALU
pbinop (Ocmpu Clt) = tok LESSU
pbinop (Ocmpu Cle) = tok LESSEQUALU
pbinop (Ocmpu Cgt) = tok GREATERU
pbinop (Ocmpu Cge) = tok GREATEREQUALU
-- pbinop (Oixleq n)  = sexp IXLEQA [pmachint n]

parea :: Area -> Doc
parea (Stored c)  = sexp STOREDA [pty c]
parea (Array a i) = sexp ARRAYA [parea a,integer i]
parea (Struct v)  = sexp STRUCTA [pvar v]

ptylist :: [Ftyp] -> Doc
ptylist ts = slist (map pty ts)

pty :: Ftyp -> Doc
pty Funit           = tok TUNIT
pty (Fint)          = tok INT32
pty (Ftcon tc)      = sexp TCONT [pvar tc]
pty (Frecordt tc n) = sexp TRECORDT [pvar tc, integer n]
pty (Ffun args res) = sexp TFUNT [ptylist args, pty res]
pty (Fix i)         = sexp TIXT [pmachint i]
pty (Fnzero)        = sexp TNZERO []
pty (Fref a)        = sexp TREFT [parea a]
pty (Fptr a)        = sexp TPTR [parea a]

patom :: Atom -> Doc
patom (Agvar v t)         = sexp GVARA [pvar v, pty t]
patom (Avar v t)          = sexp VARA [pvar v, pty t]
patom (Aconst c)          = sexp CONSTA [pconst c]
patom (Aload a n t)       = sexp LOADA [patom a, integer n, pty t]
patom (Aat a b ar)        = sexp ATA [patom a, patom b, parea ar]
patom (Asel a n ar)       = sexp SELA [patom a,integer n, parea ar]
patom (Aunop u a)         = sexp UNOPA [punop u, patom a]
patom (Abinop a b c)      = sexp BINOPA [pbinop a, patom b, patom c]

psimpleexp :: SimplExpr -> Doc
psimpleexp (Satom a)          = sexp ATOME [patom a]
psimpleexp (Scall sig v args) = sexp CALLE [psig sig, pvar v, patomlist args]
psimpleexp (Sapp sig a args)  = sexp APPE [psig sig, patom a, patomlist args]
psimpleexp (Salloc tc n args) = sexp ALLOCE [pvar tc,integer n, patomlist args]

psig :: Fsignature -> Doc
psig (Fsignature args res) = slist [ptylist args, pty res]

patomlist :: [Atom] -> Doc
patomlist ats = slist [hsep (map patom ats)]

pparams :: [(Id, Ftyp)] -> Doc
pparams = slist . map one
  where one (v, t) = parens (pvar v <+> pty t)

pbinds :: [(Id, Function)] -> Doc
pbinds b = vslist (map pbind b)

pbind :: (Id,Function) -> Doc
pbind (v, Function params t body) = slist [pvar v, pparams params, pty t, pexp body]

palts :: [(Id, Nat, Expr)] -> Doc
palts = slist . map one
  where one (v, n, e) = slist [pvar v, integer n, pexp e]

pdef :: Maybe (Id, Expr) -> Doc
pdef Nothing        = slist []
pdef (Just (v, e))  = slist [pvar v, pexp e]

pexp :: Expr -> Doc
pexp (Eatom a)           = sexp ATOME [patom a]
pexp (Elet v t rhs e)    = sexp LETE [pvar v, pty t, psimpleexp rhs, pexp e]
pexp (Eletrec functs e)  = sexp LETRECE [pbinds functs, pexp e]
pexp (Eifthenelse a b c) = sexp IFE [patom a, pexp b, pexp c]
pexp (Ecase a alts def)  = sexp CASEE [patom a, palts alts, pdef def]
pexp (Eixcase a i v b c) = sexp IXCASEE [patom a, pmachint i, pvar v, pexp b, pexp c]
pexp (Eerror t)          = sexp ERRORE [pty t]
pexp (Eletlabel functs e)= sexp LETLABELE [pbinds functs, pexp e]
pexp (Egoto l args t)    = sexp GOTOE [pvar l, patomlist args, pty t]
pexp (Enzcase _ _ _ _ )  = undefined
pexp (Erefcase _ _ _ _ _)  = undefined

ptcons :: [(Id, [[Ftyp]])] -> Doc
ptcons tcs = vslist (map pconstr tcs)
  where pconstr (tc,tyss) = parens (pvar tc <+> slist(map ptylist tyss))

pareaDecls :: [(Id, Area, Volatility, Int)] -> Doc
pareaDecls aDecls = vslist (map pArea aDecls)
  where pArea (v,a,w,s) = parens (pvar v <+> parea a <+> pvolatility w <+> int s)

pvolatility :: Volatility -> Doc
pvolatility Volatile = tok VOLATILE
pvolatility Nonvolatile = tok NONVOLATILE

pstructDecls :: [(Id, StructDesc)] -> Doc
pstructDecls ss = vslist (map pSd ss)
  where pSd (sName, StructDesc width ofsMap) =
          slist [pvar sName, integer width, parens (pstructoffsets ofsMap)]

pstructoffsets :: [(Nat, Area)] -> Doc
pstructoffsets = hsep . (map one)
  where one (i,a) = parens (integer i <+> parea a)

pcmtyp :: CMTyp -> Doc
pcmtyp (CMInt) = tok INT
pcmtyp (CMFloat) = tok FLOAT

pcmsig :: CMSignature -> Doc
pcmsig (CMSig args res) = slist [slist (map pcmtyp args), opt res]
   where opt Nothing =  empty
         opt (Just cmt) = pcmtyp cmt

pfunct :: Function -> Doc
pfunct (Function params res body) = vslist [pparams params, pty res, pexp body]

pfundec :: (Id,Fundec) -> Doc
pfundec (f, Internal (Function params res body)) = slist [pvar f,pparams params,pty res,pexp body]
pfundec (f, External ef) = slist $ [tok EXTERN, pvar f, pexternalfunc ef]

pglobal :: (Id, Global) -> Doc
pglobal (g, Global t e) = slist $ [pvar g, pty t, pexp e]

pexternalfunc :: ExternalFunction -> Doc
pexternalfunc (EFexternal iden cmsig) = slist $ [tok EXTERNAL, pid (fromString iden), pcmsig cmsig]
pexternalfunc (EFbuiltin iden cmsig) = slist $ [tok BUILTIN, pid (fromString iden), pcmsig cmsig]
pexternalfunc (EFvload memchunk) = slist $ [tok VLOAD, pmemchunk memchunk]
pexternalfunc (EFvstore memchunk) = slist $ [tok VSTORE, pmemchunk memchunk]
pexternalfunc (EFmemcpy size alignment) = slist $ [tok MEMCPY, int size, int alignment]

pmemchunk :: MemoryChunk -> Doc
pmemchunk MCint8signed = text "int8s"
pmemchunk MCint8unsigned = text "int8u"
pmemchunk MCint16signed = text "int16s"
pmemchunk MCint16unsigned = text "int16u"
pmemchunk MCint32 = text "int32"
pmemchunk MCfloat32 = text "float32"
pmemchunk MCfloat64 = text "float64"

pglobals :: [(Id, Global)] -> Doc
pglobals = parens . vcat . (map pglobal)

pfundecs :: [(Id, Fundec)] -> Doc
pfundecs = parens . vcat . (map pfundec)

pprogram :: Program -> Doc
pprogram (Program globals funs mainId initFun tconEnv areaDecls structDecls) =
  vslist
       [pvar initFun,
        pvar mainId,
        ptcons tconEnv,
        pareaDecls areaDecls,
        pstructDecls structDecls,
        pglobals globals,
        pfundecs funs]
