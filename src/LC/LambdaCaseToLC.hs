{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, DeriveDataTypeable #-}
module LC.LambdaCaseToLC (lambdaCaseToLC) where

import Common
import Syntax.Common
import qualified Syntax.LambdaCase as C
import qualified Syntax.LC as L

lambdaCaseToLC :: L.Entrypoints -> Pass () C.Program L.Program
lambdaCaseToLC entries (C.Program decls topDecls) =
  liftBase $ return (L.Program entries
                               (mDecls decls)
                               (filter (not . builtin) (mTopDecls topDecls)))
        -- hack to get around the fact that Unit is built-in
        -- in lcc.
  where builtin (L.Datatype (Ident "Unit" _ _) _ _)    = True
        builtin (L.Bitdatatype (Ident "Bool" _ _) _ _) = True
        builtin _                                      = False

-- hack to get around the fact that (not bitdata) Bool is built into lcc.
-- don't need to worry about capture since nothing on the left is a valid
-- type variable name... also, this pass is running after specialization.
s :: String -> String
-- Right now, all mappings are commented out, so this substitution does
-- nothing.
--s "True" = "TRUE"
--s "False"= "FALSE"
--s "Bool" = "BOOL"
s x      = x

sid :: Id -> Id
sid (Ident i n f) = Ident (s i) n f

st :: L.Type -> L.Type
st (L.TyCon (Kinded i k)) = L.TyCon (Kinded (sid i) k)
st (L.TyApp t1 t2)        = L.TyApp (st t1) (st t2)
st (L.TyLit n)            = L.TyLit n
-- TODO extending to labels is suspect, appears to be necessary
-- because subsitution hits constructor names, which correspond
-- to labels in BitdataCase.
st (L.TyLabel i)          = L.TyLabel (sid i)

-- I suppose 'm' is for "massage".

mDecls :: C.Decls -> L.Decls
mDecls (C.Decls dcs) = L.Decls
                     . concatMap mDecl
                     $ dcs
  where mDecl (C.Mutual dns) = map f dns
        mDecl (C.Nonrec dn)    = [f dn]
        f = L.Decl . mDefn

mDefn :: C.Defn -> L.Defn
mDefn (C.Defn id t (Left (i,ts)))  = L.Defn id (st . convert $ t) (Left (i, map (st . convert) ts))
mDefn (C.Defn id t (Right e)) = L.Defn id (st . convert $ t) (Right (mExpr e))

mExpr :: C.Expr -> L.Expr
mExpr (C.EVar i t)        = L.EVar i (st . convert $ t)
mExpr (C.EBits n s)       = L.EBits n s
mExpr (C.ENat n)          = L.ENat n
mExpr (C.ECon i ts t)     = L.ECon (sid i) (map (st . convert) ts) (st . convert $ t)
mExpr (C.EBitCon i es)    = L.EBitCon (sid i) (map (\(f, e) -> (f, mExpr e)) es)
mExpr (C.EStructInit k fs) = L.EStructInit (sid k) (map (\(f, e) -> (f, mExpr e)) fs)
mExpr (C.ELam i t e)      = L.ELam i (st . convert $ t) (mExpr e)
mExpr (C.ELet dcs e)      = L.ELet (mDecls dcs) (mExpr e)
mExpr (C.ECase e as)      = L.ECase (mExpr e) (map mAlt as)
mExpr (C.EApp e1 e2)      = L.EApp (mExpr e1) (mExpr e2)
mExpr (C.EBitSelect e f)  = L.EBitSelect (mExpr e) f
mExpr (C.EBitUpdate e f e') = L.EBitUpdate (mExpr e) f (mExpr e')
mExpr (C.EFatbar e1 e2)   = L.EFatbar (mExpr e1) (mExpr e2)
mExpr (C.EBind i t e1 e2) = L.EDo $ L.EBind i (st . convert $ t) (mExpr e1) (collateDoBlock e2)
mExpr (C.EReturn e)       = L.EReturn (mExpr e)

collateDoBlock :: C.Expr -> L.Expr
collateDoBlock (C.EBind i t e1 e2) = L.EBind i (st . convert $ t) (mExpr e1) (collateDoBlock e2)
collateDoBlock e                   = mExpr e

mAlt :: C.Alt -> L.Alt
mAlt (C.Alt i ts is e) = L.Alt (sid i) (map (st . convert) ts) is (mExpr e)

mBitdataField :: C.BitdataField -> L.BitdataField
mBitdataField (C.LabeledField i t n m) = L.LabeledField i (st . convert $ t) n m
mBitdataField (C.ConstantField n m o)  = L.ConstantField n m o

mStructField :: C.StructField -> L.StructField
mStructField (C.StructField mid t n m) = L.StructField mid (st . convert $ t) n m

mCtor :: (Id, [C.Type]) -> (Id, [L.Type])
mCtor (i, ts) = (sid i, map (st . convert) ts)

mBCtor :: (Id, [C.BitdataField]) -> (Id, [L.BitdataField])
mBCtor (i, bfs) = (sid i, map mBitdataField bfs)

mTopDecl :: C.TopDecl -> L.TopDecl
mTopDecl (C.Datatype i ts ctors)    = L.Datatype (sid i) (map (st . convert) ts) (map mCtor ctors)
mTopDecl (C.Bitdatatype i n bctors) = L.Bitdatatype (sid i) n (map mBCtor bctors)
mTopDecl (C.Struct i n sfs)         = L.Struct i n (map mStructField sfs)
mTopDecl (C.Area i v e t n m)       = L.Area i v (mExpr e) (st . convert $ t) n m

mTopDecls :: C.TopDecls -> L.TopDecls
mTopDecls = map mTopDecl
