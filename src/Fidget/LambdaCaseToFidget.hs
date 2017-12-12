{-# LANGUAGE PatternGuards, ParallelListComp, OverloadedStrings #-}

module Fidget.LambdaCaseToFidget where

-- This pass converts LambdaCase code to Fidget code.

{- Known Limitations and Problems:

- No LE or BE.
- For ARef, only alignment 1 is supported.
- No Ptr [this will require Fidget extensions]
- No nonzero support for Unsigned or Bit [will require Fidget extensions]

- No top-level non-lambdas.

- No good error messages when unsupported features are hit.

- Translation of matches produces lots of extra join points.
(These an be removed by post-optimization, but it might be good
to try to avoid generating them in the first place.)

-}

import Common
import Fidget.Env
import Fidget.Typing
import Fidget.Pretty
import qualified Fidget.AST as F
import Printer.LambdaCase
import Syntax.Common
import Syntax.LambdaCase
import qualified Typechecker.LambdaCasePrims as LCP
import qualified Typechecker.LambdaCaseTyping as LCT

import Control.Monad
import Control.Monad.Reader hiding (reader)
import Data.Bits
import Data.Either
import Data.List
import Data.Maybe

transLCtoFidget :: Id -> Id -> Pass () Program F.Program
transLCtoFidget main initialize (Program decls topDecls) = liftBase $ do
  let areas' = trans_areas topDecls
  -- TODO: toString instead of fresh
  read8 <- fresh "__builtin_volatile_read_int8unsigned"
  read16 <- fresh "__builtin_volatile_read_int16unsigned"
  read32 <- fresh "__builtin_volatile_read_int32"
  write8 <- fresh "__builtin_volatile_write_int8unsigned"
  write16 <- fresh "__builtin_volatile_write_int16unsigned"
  write32 <- fresh "__builtin_volatile_write_int32"
  let readEnv = [(8, read8), (16, read16), (32, read32)]
  let writeEnv = [(8, write8), (16, write16), (32, write32)]
  bindings <-
    runReaderT (withVarBinds [(x, VarBind (F.Aconst (F.Oarea x a)) Nothing)
                                | (x, a, _, _) <- areas']
                (trans_prog_decls senv cenv readEnv writeEnv decls))
               empty_env
  return $ F.Program
           [(x,g) | (x, Left g) <- bindings]
           (map (\(size, id) -> (id, F.External (F.EFvstore (mem_chunk size)))) writeEnv ++
            map (\(size, id) -> (id, F.External (F.EFvload  (mem_chunk size)))) readEnv ++
            [(x,f) | (x, Right f) <- bindings])
           main
           initialize
           (trans_datatypes topDecls)
           areas'
           (trans_structs topDecls)
  where senv = build_struct_env topDecls
        cenv = build_con_env topDecls
        mem_chunk :: Int -> F.MemoryChunk
        mem_chunk 8  = F.MCint8unsigned
        mem_chunk 16 = F.MCint16unsigned
        mem_chunk 32 = F.MCint32

type M a = ReaderT VarEnv Base a -- The monad used for translating everything other than F.Expr.
type M' a = ReaderT (F.Expr, F.Ftyp) (ReaderT VarEnv Base) a -- The monad used for translating to F.Expr.  Stores the expected result type which is used by F.Egoto.  Also stores the expression to use for backtracking.

withExpectedType :: F.Expr -> F.Ftyp -> M' a -> M a
withExpectedType e t m = runReaderT m (e, t)
withBacktrackLabel :: F.Label -> M' a -> M' a
withBacktrackLabel l m = local (\(_, t) -> (F.Egoto l [] t, t)) m
readBacktrack :: M' (F.Expr)
readBacktrack = asks fst

withVarBinds :: [(Id, VarBind)] -> M a -> M a
withVarBinds bs m = local (\env -> foldl (\env (id, b) -> extend_env env id b) env bs) m
withVarBinds' :: [(Id, VarBind)] -> M' a -> M' a
withVarBinds' bs m = do
  et <- ask
  lift $ local (\env -> foldl (\env (id, b) -> extend_env env id b) env bs) (runReaderT m et)
getVarBind :: Id -> M' VarBind
getVarBind x = lift $ asks (flip lookup_env x)

{- Various useful translation environments -}

newtype StructBind = StructBind [(Id,Int)] -- field name, offset in bytes

type StructEnv = Env Id StructBind

data ConBind = ConBind {fields::[F.Ftyp],
                        tcon::F.Tcon,
                        tag::Integer}
             | BitdataConBind {tagmask:: Integer,
                               tagbits:: Integer,
                               bfields::[(Id,Int,Int)] -- field name, width, offset in bits
                              }

type ConEnv = Env (Id,[Type]) ConBind

data VarBind = VarBind {transl :: F.Atom,
                        known :: Maybe Bool}  -- known function: istoplevel?

type VarEnv = Env Id VarBind

{- Translation of various Kinds of Types -}

trans_type_nat :: Type -> F.Nat
trans_type_nat (TyLit n) = n
trans_type_nat ty = error ("impossible trans_type_nat:" ++ (show (ppr ty)))

trans_type_machint :: Type -> F.Machint
trans_type_machint (TyLit n) = checked_to_machint n
trans_type_machint ty = error ("impossible trans_type_machint:" ++ (show (ppr ty)))

trans_type_area :: Type -> F.Area
trans_type_area ty =
  case ty of
    TyApp (TyApp (TyCon (Kinded "Array" _)) ty_n) ty_a ->
      F.Array (trans_type_area ty_a) (trans_type_nat ty_n)
    TyApp (TyCon (Kinded "Stored" _)) ty ->
      F.Stored (trans_type_star ty)
    TyCon (Kinded sid KArea) -> F.Struct sid
    _ -> error ("impossible trans_type_area:" ++ (show (ppr ty)))

trans_type_star :: Type -> F.Ftyp
trans_type_star ty =
  case ty of
    TyApp (TyApp(TyCon (Kinded "->" _)) ty1) ty2 ->
        F.Ffun [trans_type_star ty1] (trans_type_star ty2)
    TyCon (Kinded "NonZero" _) -> F.Fnzero
    TyApp (TyCon (Kinded "Nat" _)) ty_n -> F.Funit
    TyApp (TyCon (Kinded "Ix" _)) ty_n -> F.Fix (trans_type_machint ty_n) -- always in range
    TyApp (TyCon (Kinded "Bit" _)) ty_n -> F.Fint  -- ignore high order bits
    TyApp (TyApp(TyCon (Kinded "ARef" _)) (TyLit 1)) ty_a -> F.Fref (trans_type_area ty_a) -- for now force alignment to be 1
    TyApp (TyApp(TyCon (Kinded "APtr" _)) (TyLit 1)) ty_a -> F.Fptr (trans_type_area ty_a) -- for now force alignment to be 1
    TyApp (TyApp (TyCon (Kinded "BitdataCase" (KFun KStar (KFun KLabel KStar)))) _) _ -> F.Fint
    TyCon (Kinded t KStar) -> F.Ftcon t
    _ -> error $ "Internal error: Unexpected type: " ++ show ty

build_struct_env :: [TopDecl] -> StructEnv
build_struct_env tds = foldl build empty_env tds
  where build :: StructEnv -> TopDecl -> StructEnv
        build env (Struct sid _ fs) =
          extend_env env sid (StructBind (map (\(StructField id _ _ offset) -> (fromJust id,offset)) fs'))
            where fs' = filter (\(StructField id _ _ _) -> isJust id) fs
        build env _ = env

-- build mapping from (dcon id, instantiating types) to fidget dcon info
build_con_env :: [TopDecl] -> ConEnv
build_con_env tds = foldr build empty_env tds
  where build :: TopDecl -> ConEnv -> ConEnv
        build (Datatype tc ts cs) env =
             foldr (\(tag,(c,cts)) env ->
                      extend_env env (c,ts) (ConBind (map trans_type_star cts) tc tag))
                     env (zip [0..] cs)
        build (Bitdatatype _ _ dcs) env =
          foldr (\(c,flds) env -> extend_env env (c,[]) (build_bitdata_bind flds)) env dcs
        build _ env = env -- for now

build_bitdata_bind :: [BitdataField] -> ConBind
build_bitdata_bind flds = BitdataConBind tagmask tagbits lfields
  where (lfields,cfields) =
         foldr (\f (lfs,cfs) ->
                     case f of
                      LabeledField x _ width offset -> ((x,width,offset):lfs,cfs)
                      ConstantField v width offset -> (lfs,(v,width,offset):cfs)) ([],[]) flds
        tagmask = foldr (\(_,width,offset) m -> ((2^width - 1) `shift` offset) .|. m) 0 cfields
        tagbits = foldr (\(v,width,offset) b -> (v .&. (2^width - 1) `shift` offset) .|. b) 0 cfields

trans_datatypes :: [TopDecl] -> [(F.Id,[[F.Ftyp]])]
trans_datatypes tds = foldr trans [] tds
   where trans :: TopDecl -> [(F.Id,[[F.Ftyp]])] -> [(F.Id,[[F.Ftyp]])]
         trans (Datatype tc ts cs) l = (tc, map (\(_,cts) -> map trans_type_star cts) cs):l
         trans _ l = l

trans_areas :: [TopDecl] -> [(Id, F.Area, F.Volatility, Int)]
trans_areas tds = foldl trans [] tds
   where trans :: [(Id, F.Area, F.Volatility, Int)] -> TopDecl -> [(Id, F.Area, F.Volatility, Int)]
         trans l (Area x v _ (TyApp (TyApp (TyCon (Kinded "ARef" _)) (TyLit 1)) a) size _) =
           (x, trans_type_area a, volatility, size) : l where
             volatility = if v then F.Volatile else F.Nonvolatile
         trans l (Area _ _ _ _ _ _) = error "trans_area bad area type"
         trans l _ = l

trans_structs :: [TopDecl] -> [(F.Id,F.StructDesc)]
trans_structs tds = foldr trans [] tds
   where trans :: TopDecl -> [(F.Id,F.StructDesc)] -> [(F.Id,F.StructDesc)]
         trans (Struct sid width sfields) l =
             let sfields' = map (\(StructField _ ft _ fo) ->
                                   (fromIntegral fo, trans_type_area ft)) sfields in
             (sid,F.StructDesc (fromIntegral width) sfields'):l
         trans _ l = l

curry_Ftype :: [F.Ftyp] -> F.Ftyp -> F.Ftyp
curry_Ftype [] t0 = t0
curry_Ftype (t:ts) t0 = F.Ffun [t] (curry_Ftype ts t0)

{- transform program-level declaration group -}
trans_prog_decls :: StructEnv -> ConEnv -> [(Int, Id)] -> [(Int, Id)] -> Decls -> M [(F.Id,Either F.Global F.Fundec)]
trans_prog_decls senv cenv readEnv writeEnv decls = trans_top_decls decls where

  prims = [p | let Decls ds = decls, Just p <- map getPrim ds]

  getPrim :: Decl -> Maybe (Id, (Type, String, [Type]))
  getPrim (Nonrec (Defn id typ (Left (str, typ_args)))) = Just (id, (typ, str, typ_args))
  getPrim _ = Nothing

  ftype_of :: Expr -> F.Ftyp
  ftype_of e = trans_type_star (LCT.type_of e)

  name :: F.SimplExpr -> F.Ftyp -> (F.Atom -> M' F.Expr) -> M' F.Expr
  name (F.Satom a) t k = k a
  name s t k = do a <- fresh "a$"
                  ka <- k (F.Avar a t)
                  return $ F.Elet a t s ka

  gotoLabel :: F.Label -> F.Atom -> M' F.Expr
  gotoLabel l a = do (_, t) <- ask; return $ F.Egoto l [a] t

  atomize :: Expr -> (F.Atom -> M' F.Expr) -> M' F.Expr
  atomize e k = -- picking apart *result* of translation is inconsistent, but useful
    trans_expr e (\s -> name s (ftype_of e) k)

  -- a little crude
  is_bitdata :: Type -> Bool
  is_bitdata = (==LCP.bits (LCP.natT LCP.word_size))

  trans_expr :: Expr -> (F.SimplExpr -> M' F.Expr) -> M' F.Expr
  trans_expr = trans_expr' []

  trans_expr' :: [Expr] -> Expr -> (F.SimplExpr -> M' F.Expr) -> M' F.Expr
  trans_expr' [] (EBits n _) k = k $ F.Satom (F.Aconst (F.Ointconst (fromInteger n)))
  trans_expr' [] (ENat _) k = k $ F.Satom (F.Aconst F.Ounit)
  trans_expr' [] (ELet dss e0) k = trans_decls dss (trans_expr e0 k)

  -- handle bitdata
  trans_expr' [] (e0@(ECase e alts)) k | is_bitdata (LCT.type_of e) =
   atomize e (\a ->
     do lab <- fresh "l$"
        x <- fresh "x$"
        let t' = ftype_of e0
        kx <- k (F.Satom (F.Avar x t'))
        (_, returnTyp) <- ask
        body <- trans_alts lab a alts
        return $ F.Eletlabel [(lab, F.Function [(x,t')] returnTyp kx)] body)
   where trans_alts lab a (Alt c [] [x] earm:rest) =
             do let test = F.Abinop (F.Ocmp F.Ceq) (F.Abinop F.Oand a (int_const tagmask)) (int_const tagbits)
                earma <- withVarBinds' [(x, VarBind a Nothing)] $
                         atomize earm (gotoLabel lab)
                restm <- trans_alts lab a rest
                return $ F.Eifthenelse test earma restm
             where BitdataConBind tagmask tagbits _ = lookup_env cenv (c,[])
         trans_alts lab a [] = readBacktrack

{-
  -- could hack a special case for boolean bit data cases
  trans_expr' [] (e0@(ECase e [Alt "True" [] [] et,Alt "False" [] [] ef])) k =
    atomize e (\a ->
       do lab <- fresh "l$"
          tarma <- atomize et (gotoLabel lab)
          farma <- atomize ef (gotoLabel lab)
          x <- fresh "x$"
          let t' = ftype_of e0
          kx <- k (F.Satom (F.Avar x t'))
          return $ F.Eletlabel (lab,[(x,t')],kx)
                        (F.Eifthenelse (F.Abinop F.Oand a (int_const 1)) tarma farma))
  trans_expr (ECase e [Alt "False" [] [] ef,Alt "True" [] [] et]) k =
      trans_expr (ECase e [Alt "True" [] [] et, Alt "False" [] [] ef]) k
-}

  trans_expr' [] (e0@(ECase e alts)) k =
   atomize e (\a ->
     do lab <- fresh "l$"
        x <- fresh "x$"
        let t' = ftype_of e0
        alts' <- mapM (trans_alt lab) alts

        k' <- k (F.Satom (F.Avar x t'))
        dummy <- fresh "d$"
        defaultExpr <- readBacktrack

        (_, returnTyp) <- ask
        return $ F.Eletlabel [(lab, F.Function [(x,t')] returnTyp k')]
                 (F.Ecase a alts' (Just (dummy, defaultExpr))))
   where trans_alt lab (Alt c ts xs earm) =
             do aa <- fresh "d$"
                earma <- withVarBinds' [
                          (x, VarBind (F.Aload (F.Avar aa (F.Frecordt tcon tag)) ofs t') Nothing)
                            | x <- xs | ofs <- [0..] | t' <- ts'] $
                         atomize earm (gotoLabel lab)
                return (aa,tag,earma)
             where ConBind ts' tcon tag = lookup_env cenv (c,ts)

  trans_expr' [] (e@(EFatbar e1 e2)) k =
   do exitlab <- fresh "l$"
      joinlab <- fresh "l$"
      x <- fresh "x$"
      let t' = ftype_of e
      e1a <- withBacktrackLabel exitlab $ atomize e1 (gotoLabel joinlab)
      e2a <- atomize e2 (gotoLabel joinlab)
      k' <- k (F.Satom (F.Avar x t'))
      (_, returnTyp) <- ask
      return $ F.Eletlabel [(joinlab, F.Function [(x, t')] returnTyp k')]
               (F.Eletlabel [(exitlab, F.Function [] returnTyp e2a)] e1a)

  trans_expr' estk (EApp e1 e2) k = trans_expr' (e2:estk) e1 k

  trans_expr' [] (ELam x t e0) k = -- we can't uncurry here, because we lack a name to bind to
     do f <- fresh "f$"
        func  <- lift (trans_lam [(x,t)] e0)
        kk <- k (F.Satom (F.Avar f (F.Ffun [trans_type_star t] (ftype_of e0))))
        return $ F.Eletrec [(f,func)] kk
   {- The following case is important to clean up after preprocessing to put in force/delay.
      Otherwise, we probably won't see many of these.
      The treatment is a bit half-hearted, since we process the RHS of the Elet without
      knowing that it is named (hence no uncurrying of functions, for example) -}
  trans_expr' (e1:estk) (ELam x t e0) k =
    atomize e1 (\a -> withVarBinds' [(x, VarBind a Nothing)] $ trans_expr' estk e0 k)
  trans_expr' estk (EVar x _) k
    | Just (typ, str, typ_args) <- lookup x prims = do
      let (ts', t') = unwind_type (trans_type_star typ)
      eta_or_app ts' t' estk [] (trans_prim x str typ typ_args) k
    | otherwise = do
      VarBind a' known <- getVarBind x
      case (known, type_of_atom a') of
        (Just toplevel, F.Ffun ts' t') {- | (length ts' > 1) -} ->
          eta_or_app ts' t' estk [] f k
            where f as' k' | toplevel = let F.Avar x' _ = a'
                                        in k' $ F.Scall (F.Fsignature ts' t') x' as'
                           | otherwise = k' $ F.Sapp (F.Fsignature ts' t') a' as'
        _ -> eta_or_app [] (type_of_atom a') estk [] (\([]) k' -> k' (F.Satom a')) k
  trans_expr' estk (ECon c ts _) k | ConBind ts' tcon tag <- lookup_env cenv (c,ts) =
    eta_or_app ts' (F.Frecordt tcon tag) estk [] (\as' k' -> k' (F.Salloc tcon tag as')) k
  trans_expr' [e] (ECon c ts _) k | BitdataConBind _ _ _ <- lookup_env cenv (c,ts) =
    atomize e (k . F.Satom)

  trans_expr' estk e k =
    trans_expr e (\s -> eta_or_app [] (ftype_of e) estk [] (\([]) k -> k s) k)

  -- This function does whatever magic is needed in order to use the 'call builder'
  -- with the number of arguments that it expects.
  eta_or_app :: [F.Ftyp] {-argument types of call builder-}
             -> F.Ftyp {-result type of call builder-}
             -> [Expr] {-unprocessed args-}
             -> [F.Atom] {-processed args-}
             -> ([F.Atom] -> (F.SimplExpr -> M' F.Expr) -> M' F.Expr) {-call builder-}
             -> (F.SimplExpr -> M' F.Expr) {-continuation/context-}
             -> M' F.Expr
  eta_or_app [] _ [] bs f k = f bs k
  eta_or_app (t:ts) t0 (a:as) bs f k = atomize a (\a' -> eta_or_app ts t0 as (bs++[a']) f k)
  eta_or_app (t:ts) t0 [] bs f k = do
    -- The builder expects more arguments than we have so build a curried function
    -- letrec f' a = [eta (++a) f] in [k f']
    f' <- fresh "f$"
    a <- fresh "a$"
    let rt = curry_Ftype ts t0
    body <- eta_or_app ts t0 [] (bs ++ [F.Avar a t]) f (\s -> name s rt (return . F.Eatom))
    k' <- k (F.Satom (F.Avar f' (F.Ffun [t] rt)))
    return $ F.Eletrec [(f', F.Function [(a, t)] rt body)] k'
  eta_or_app [] (F.Ffun [ts] t) as bs f k = do
    -- The builder expects fewer arguments than we have so build F.Sapp calls
    -- let x = [f bs] in [eta .. [\y -> x y] k]
    f bs (\s -> name s (F.Ffun [ts] t) (\x -> eta_or_app [ts] t as [] (f' x) k))
    where f' :: F.Atom -> [F.Atom] -> (F.SimplExpr -> M' F.Expr) -> M' F.Expr
          f' x [a] k = k $ F.Sapp (F.Fsignature [ts] t) x [a]

  {- transform a fully saturated primitive application -}
  {- we may not need this much generality, but keep it for now -}
  trans_prim :: Id -> String -> Type -> [Type] -> [F.Atom] -> (F.SimplExpr -> M' F.Expr) -> M' F.Expr
  trans_prim id p t ts as k
    | Just f <- lookup p (prim_table senv cenv readEnv writeEnv) = f ts as k
    | otherwise = k $ F.Scall (F.Fsignature args ret) id as
        where (args, ret) = unwind_type (trans_type_star t)

  funBind :: Id -> Id -> [(Id, Type)] -> Expr -> Bool -> (Id, VarBind)
  funBind oldId newId xts e topLevel =
    (oldId, VarBind
            (F.Avar newId (F.Ffun (map (trans_type_star . snd) xts) (ftype_of e)))
            (Just topLevel))

  {- transform an uncurried lambda -}
  trans_lam :: [(Id,Type)] -> Expr -> M F.Function
  trans_lam xts e = do
    xs' <- mapM (fresh . fst) xts
    let ts' = map (trans_type_star . snd) xts
    let t' = ftype_of e
    e' <- withExpectedType (F.Eerror t') t' $
          withVarBinds' [(x, VarBind (F.Avar x' t') Nothing)
                         | (x, _) <- xts | x' <- xs' | t' <- ts'] $
          atomize e (return . F.Eatom)
    return $ F.Function (zip xs' ts') t' e'

  {- transform a Let-bound declaration group -}
  trans_decls :: Decls -> M' F.Expr -> M' F.Expr
  trans_decls (Decls []) k = k
  trans_decls (Decls (ds:dss)) k =
       trans_decl ds (trans_decls (Decls dss) k)

  {- handle a simple non-recursive declaration -}
  trans_decl :: Decl -> M' F.Expr -> M' F.Expr
  trans_decl (Nonrec (Defn x t (Right e0))) k =
   do x' <- fresh x
      case uncurry_lam e0 of
        ([], e) -> do let t' = trans_type_star t
                      body' <- withVarBinds' [(x, VarBind (F.Avar x' t') Nothing)] $ k
                      trans_expr e0 (\s -> return $ F.Elet x' t' s body')
        (xts, e) -> do func <- lift $ trans_lam xts e
                       body' <- withVarBinds' [funBind x x' xts e False] $ k
                       return $ F.Eletrec [(x',func)] body'
  {- handle recursive group of named lambdas, uncurrying as we go -}
  trans_decl (Mutual ds) k =
   do let fs = map (\(Defn f _ _) -> f) ds -- original function names
      fs' <- mapM fresh fs -- new function names
      let ucs = map uncurry_lam (map (\(Defn _ _ (Right e)) -> e) ds)
      {- the following is a bit ugly, because trans_lam is going to translate the
         types again in a moment anyway... -}
      let varBinds = [funBind f f' xts e False | f <- fs | f' <- fs' | (xts, e) <- ucs]
      ucs' <- withVarBinds' varBinds $ mapM (\(xts, e) -> lift $ trans_lam xts e) ucs
      k' <- withVarBinds' varBinds $ k
      return $ F.Eletrec (zip fs' ucs') k'

  uncurry_lam :: Expr -> ([(Id, Type)], Expr)
  uncurry_lam (ELam x t expr) = ((x, t) : vars, expr0)
    where (vars, expr0) = uncurry_lam expr
  uncurry_lam expr = ([], expr)

  {- transform a top-level declaration group -}
  trans_top_decls :: Decls -> M [(F.Id,Either F.Global F.Fundec)]
  trans_top_decls (Decls []) = return []
  trans_top_decls (Decls (ds:dss)) =
       do (varBinds, fs) <- trans_top_decl ds
          fss <- withVarBinds varBinds $ trans_top_decls (Decls dss)
          return (fs++fss)

  {- note: once handling of non-lambdas settles down, we should refactor so that
     this function and trans_decl are a single function.
     However, an importand difference from trans_decl is that
     we do not rename top level names. -}
  trans_top_decl :: Decl -> M ([(Id, VarBind)],[(F.Id,Either F.Global F.Fundec)])
  {- single ordinary definition  -}
  trans_top_decl (Nonrec (Defn x t (Left (str, typ_args)))) =
    if str `elem` known_prims
    then return ([], [])
    else return ([], [(x, Right (F.External (F.EFexternal str (F.CMSig (map ftyp args) ret'))))])
    where
      (args, ret) = unwind_type (trans_type_star t)
      ret' | F.Funit <- ret = Nothing
           | otherwise      = Just (ftyp ret)
      ftyp (F.Fint) = F.CMInt
      ftyp (F.Fix _) = F.CMInt
      ftyp (F.Fref a) = F.CMInt {- really a pointer -}
      ftyp t = error ("Unsupported extern type: " ++ show t)

  trans_top_decl (Nonrec (Defn x t (Right e0))) =
   do case uncurry_lam e0 of
        -- TODO: only word size types should be allowed
        ([], e) -> do let t' = trans_type_star t
                      e' <- withExpectedType (error "Egoto in global") t' $
                            atomize e (return . F.Eatom)
                      return ([(x, VarBind (F.Agvar x t') (Just True))],
                              [(x, Left (F.Global t' e'))])
        (xts, e) -> do func <- trans_lam xts e
                       return ([funBind x x xts e True], [(x, Right (F.Internal func))])

  {- handle recursive group of named lambdas, uncurrying as we go -}
  trans_top_decl (Mutual ds) =
   do let fs = map (\(Defn f _ _) -> f) ds -- original function names
      let ucs = map uncurry_lam (map (\(Defn _ _ (Right e)) -> e) ds)
      {- the following is a bit ugly, because trans_lam is going to translate the
         types again in a moment anyway... -}
      let varBinds = [funBind f f xts e True | f <- fs | (xts, e) <- ucs]
      ucs' <- withVarBinds varBinds $ mapM (uncurry trans_lam) ucs
      return (varBinds, zip fs (map (Right . F.Internal) ucs'))

known_prims = map fst (prim_table err err err err) where err = error "Internal error"

{- Encoding conventions:
   Bitdata and Bit use machine ints (type Fint) in which any unused high-order bits are arbitrary.
   Ix uses machine ints (type Fix) which are always maintained to be < index bound.
   Maybe Ix uses machine ints (type Fint) where any value >= index bound represents Nothing
-}
prim_table :: StructEnv -> ConEnv -> [(Int, Id)] -> [(Int, Id)]
           -> [(String{-prim name-}, [Type] -> [F.Atom] -> (F.SimplExpr -> M' F.Expr) -> M' F.Expr)]
prim_table senv cenv readEnv writeEnv = table where
  table = [
    -- TODO: prims for Onzunsigned, Optr, Enzcase and Erefcase
    ("primIncIx", \[TyLit n] [a] k ->
      (k . F.Satom) $ F.Abinop F.Oadd (F.Aunop (F.Oixunsigned (checked_to_machint n)) a) (int_const 1)),
    ("primDecIx", \[TyLit n] [a] k ->
      (k . F.Satom) $ F.Abinop F.Osub (F.Aunop (F.Oixunsigned (checked_to_machint n)) a) (int_const 1)),
    ("primMaybeIx", \[TyLit n, TyLit m] [a] k ->
      (k . F.Satom) $ a),
    ("primModIx", \[TyLit n, _] [a] k ->
      -- extra argument is from WordSize type synonym
      (k . F.Satom) $ F.Aunop (F.Omodix (checked_to_machint n)) a),
    ("primLeqIx", \[TyLit n, _] [a1,a2] k -> 
      -- extra argument is from WordSize type synonym
      -- OLD VERSION: (k . F.Satom) $ F.Abinop (F.Oixleq (checked_to_machint n)) a1 a2),
      do j <- fresh "j$"
         x <- fresh "x$"
         a1' <- fresh "a$"
         jcode <- k (F.Satom (F.Avar x F.Fint))
         (_,returnTyp) <- ask
         return $ F.Eletlabel [(j,F.Function [(x,F.Fint)] returnTyp jcode)]
                   (F.Elet a1' F.Fint (F.Satom a1) 
                   (F.Eifthenelse (F.Abinop (F.Ocmpu F.Cle) (F.Avar a1' F.Fint) (F.Aunop (F.Oixunsigned (checked_to_machint n)) a2))
                   (F.Egoto j [F.Avar a1' F.Fint] returnTyp)
                   (F.Egoto j [F.Aconst (F.Ointconst (checked_to_machint n))] returnTyp)))),
    ("primRelaxIx", \[TyLit n,TyLit m] [a] k ->
      (k . F.Satom) $ F.Aunop (F.Orelax (checked_to_machint n) (checked_to_machint m)) a),
    ("primIxEq", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop (F.Ocmp F.Ceq) (F.Aunop (F.Oixunsigned (checked_to_machint n)) a1) (F.Aunop (F.Oixunsigned (checked_to_machint n)) a2)),
    ("primIxLt", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop (F.Ocmp F.Clt) (F.Aunop (F.Oixunsigned (checked_to_machint n)) a1) (F.Aunop (F.Oixunsigned (checked_to_machint n)) a2)),
    ("primIxLe", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop (F.Ocmp F.Cle) (F.Aunop (F.Oixunsigned (checked_to_machint n)) a1) (F.Aunop (F.Oixunsigned (checked_to_machint n)) a2)),
    ("primIxMaxBound", \[TyLit n] [] k ->
      (k . F.Satom) $ F.Aunop (F.Omodix (checked_to_machint n)) (int_const (n-1))), -- since n is constant, hopefully this will end up being free
    ("primIxFromLiteral", \[TyLit n,TyLit m] [_] k ->
      (k . F.Satom) $ F.Aunop (F.Omodix (checked_to_machint m)) (int_const n)), -- since n is constant, hopefully this will end up being free
    ("primIxShiftL", \[TyLit n,TyLit m] [a1,a2] k ->
      -- the mod really shouldn't be necessary, but changing this would require another fidget prim!
      (k . F.Satom) $ F.Aunop (F.Omodix (checked_to_machint n)) (F.Abinop F.Oshl (F.Aunop (F.Oixunsigned (checked_to_machint n)) a1) (relaxIxToWordSize m a2))),
    ("primIxShiftR", \[TyLit n,TyLit m] [a1,a2] k ->
      -- the mod really shouldn't be necessary, but changing this would require another fidget prim!
      (k . F.Satom) $ F.Aunop (F.Omodix (checked_to_machint n)) (F.Abinop F.Oshru (F.Aunop (F.Oixunsigned (checked_to_machint n)) a1) (relaxIxToWordSize m a2))),
    (":#", \[TyLit m,TyLit n,TyLit p] [a1,a2] k ->
      -- hmm: now a bit expensive
      (k . F.Satom) $ (F.Abinop F.Oor (F.Abinop F.Oshl a1 (ix_const n)) (F.Abinop F.Oand a2 (int_const (2^n-1))))),
    ("primBitEq", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop (F.Ocmp F.Ceq) (F.Abinop F.Oand a1 (int_const (2^n - 1))) (F.Abinop F.Oand a2 (int_const (2^n - 1)))),
    ("primBitLt", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop (F.Ocmpu F.Clt) (F.Abinop F.Oand a1 (int_const (2^n - 1))) (F.Abinop F.Oand a2 (int_const (2^n - 1)))),
    ("primBitLe", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop (F.Ocmpu F.Cle) (F.Abinop F.Oand a1 (int_const (2^n - 1))) (F.Abinop F.Oand a2 (int_const (2^n - 1)))),
    ("primBitPlus", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oadd a1 a2),
    ("primBitMinus", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Osub a1 a2),
    ("primBitTimes", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Omul a1 a2),
    ("primBitNegate", \[TyLit n] [a] k ->
      (k . F.Satom) $ F.Aunop F.Onegint a),
    ("primBitFromLiteral", \[TyLit n,_,TyLit m] [_] k ->
      (k . F.Satom) $ int_const n),
    ("primBitBit", \[TyLit n] [a] k ->
      (k . F.Satom) $ F.Abinop F.Oshl (int_const 1) a),
    ("primBitBitSize", \[TyLit n] _ k -> k . F.Satom $ ix_const (n-1)),
    ("primBitSetBit", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oor a1 (F.Abinop F.Oshl (int_const 1) a2)),
    ("primBitClearBit", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oand a1 (F.Aunop F.Onotint (F.Abinop F.Oshl (int_const 1) a2))),
    ("primBitFlipBit", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oxor a1 (F.Abinop F.Oshl (int_const 1) a2)),
    ("primBitTestBit", \[TyLit n] [a1,a2] k ->
      -- assumes we need a firm 0 or 1; there may be better ways
      (k . F.Satom) $ F.Abinop F.Oand (F.Abinop F.Oshr a1 a2) (int_const 1)),
    ("primIxToBits", \[TyLit n,TyLit m] [a] k ->
      (k . F.Satom) $ F.Aunop (F.Oixunsigned (checked_to_machint n)) a),
    ("primIxFromBits", \[TyLit m,TyLit n] [a] k ->
      (k . F.Satom) $ F.Aunop (F.Omodix (checked_to_machint (2^n))) a),
    ("primBitAnd", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oand a1 a2),
    ("primBitOr", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oor a1 a2),
    ("primBitXor", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oxor a1 a2),
    ("primBitNot", \[TyLit n] [a] k ->
      (k . F.Satom) $ F.Aunop F.Onotint a),
    ("primBitShiftL", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oshl a1 a2),
    ("primBitShiftR", \[TyLit n] [a1,a2] k ->
      (k . F.Satom) $ F.Abinop F.Oshr a1 a2),
    ("primBitShiftRu", \[TyLit n] [a1, a2] k ->
      (k . F.Satom) $ F.Abinop F.Oshru a1 a2),
    ("primBitSignExtend", \[TyLit n] [a] k ->
      let shift_constant = ix_const (LCP.word_size - n)
      in (k . F.Satom) $ F.Abinop F.Oshr (F.Abinop F.Oshl a shift_constant) shift_constant),
    ("@", \[TyLit n,area, _, _] [a1,a2] k ->
      -- Extra type arguments are due to type synonyms
      (k . F.Satom) $ F.Aat a1 a2 (trans_type_area area)),
  
    -- bitdata
    ("constructBitdata", \[r] as k ->
      let (args,TyApp _ (TyLabel dc)) = LCT.uncurry_type r
          BitdataConBind _ tagbits fields = lookup_env cenv (dc,[])
          fvals = zipWith (\(_,width,offset) a -> bit_field a width offset) fields as
      in (k . F.Satom) $ foldl (F.Abinop F.Oor) (int_const tagbits) fvals),
    ("bitdataSelect", \[r,f0,f,t] [a,_] k ->
      case t of
        TyApp(TyCon (Kinded "Ix" _)) ty_n -> 
          -- Perhaps should issues an efficiency warning when n is not a power of 2
          let (field_width,field_offset) = lookup_bitdata_field f0 f
          in (k . F.Satom) $ F.Aunop (F.Omodix (checked_to_machint (trans_type_nat ty_n))) (F.Abinop F.Oshr a (ix_const field_offset))
        _ ->
          -- assume Bit or Bitdata, so no need to mask out high-order bits -}
          let (_,field_offset) = lookup_bitdata_field f0 f
          in (k . F.Satom) $ F.Abinop F.Oshr a (ix_const field_offset)),
    ("bitdataUpdate", \[r,f0,f,t] [a1,_,a2] k ->
      let (field_width,field_offset) = lookup_bitdata_field f0 f
      in (k . F.Satom) $ F.Abinop F.Oor (F.Abinop F.Oand a1 (bit_mask_out field_width field_offset)) (bit_field a2 field_width field_offset)),
    -- structures
    ("selectStruct", \[s,f,t] [a] k ->
      let field_offset = fromIntegral $ lookup_struct_field s f
      in (k . F.Satom) $ F.Asel a field_offset (trans_type_area t)),
  
    ("primReturnM", \[t] [a] k ->
      (k . F.Satom) $ a),
    ("primReturnI", \[t] [a] k ->
      (k . F.Satom) $ a),
    ("primInitStored", \[t] [a1,a2] k ->
      -- Really we should calculate these values, but they are not used by writeRef so we put dummy values here
      fromJust (lookup "writeRef" table) [t, error "Internal error"] [a2,a1] k),
    ("init", \[t] [a1,a2] k -> do
      f <- fresh "f$"
      let unit_to_unit = (F.Ffun [F.Funit] F.Funit)
      body <- k (F.Sapp (F.Fsignature [F.Funit] F.Funit) (F.Avar f unit_to_unit) [F.Aconst F.Ounit])
      return $ F.Elet f unit_to_unit (F.Sapp (F.Fsignature [F.Fref $ trans_type_area t] unit_to_unit) a1 [a2]) body),
    ("uninit", \[t] [a1,a2] k ->do
      f <- fresh "f$"
      let unit_to_unit = (F.Ffun [F.Funit] F.Funit)
      body <- k (F.Sapp (F.Fsignature [F.Funit] F.Funit) (F.Avar f unit_to_unit) [F.Aconst F.Ounit])
      return $ F.Elet f unit_to_unit (F.Sapp (F.Fsignature [F.Fref $ trans_type_area t] unit_to_unit) a1 [a2]) body),
  
    -- Primitives that involve actual calls
    ("writeRef", \[t, _] [a1,a2] k ->
      -- Extra type argument is due to type synonyms
      let area' = trans_type_area (LCP.stored t)
          t'' = trans_type_star t
          Just id = lookup (stored_size t'') writeEnv
      in k $ F.Scall (F.Fsignature [F.Fref area',t''] F.Funit) id [a1,a2]),
    ("readRef", \[t, _] [a] k ->
      -- Extra type argument is due to type synonyms
      let area' = trans_type_area (LCP.stored t)
          t'' = trans_type_star t
          Just id = lookup (stored_size t'') readEnv
      in k $ F.Scall (F.Fsignature [F.Fref area'] t'') id [a])]

  lookup_bitdata_field :: Type -> Type -> (Int,Int)
  lookup_bitdata_field (TyLabel dcon) (TyLabel id) | BitdataConBind _ _ fields <- lookup_env cenv (dcon,[]) =
    find fields
      where find :: [(Id,Int,Int)] -> (Int,Int)
            find [] = error "lookup_bitdata_field failed"
            find ((field,width,offset):fields) | (field == id) = (width,offset)
            find (_:fields) = find fields
  lookup_bitdata_field _ _ = error "lookup_bitdata_field impossible"
  
  bit_field :: F.Atom -> Int -> Int -> F.Atom
  bit_field v width offset = F.Abinop F.Oshl (F.Abinop F.Oand v (int_const (2^width - 1))) (ix_const offset)
  
  bit_mask_out :: Int -> Int -> F.Atom
  bit_mask_out width offset = int_const (complement (((2^width - 1)::Int) `shift` offset))
  
  lookup_struct_field :: Type -> Type -> Int
  lookup_struct_field (TyCon(Kinded sid KArea)) (TyLabel id) | StructBind sfields <- lookup_env senv sid =
    find sfields
      where find :: [(Id,Int)] -> Int
            find [] = error "lookup_struct_field failed"
            find ((field,offset):sfields) | (field == id) = offset
            find (_:sfields) = find sfields
  lookup_struct_field _ _ = error "lookup_struct_field impossible"

-- map (type) -> (arg types, result type)
-- note that we should unwind *after* translation, because trans_type_star might raise
-- the arity further (e.g. for monadic types)
unwind_type :: F.Ftyp -> ([F.Ftyp],F.Ftyp)
unwind_type t = unwind [] t
   where unwind args (F.Ffun ts t) = unwind (args++ts) t
         unwind args t = (args,t)

relaxIxToWordSize :: Integer -> F.Atom -> F.Atom
relaxIxToWordSize x a | x == LCP.word_size = a
relaxIxToWordSize n a
  | n < 32    = F.Aunop (F.Orelax (checked_to_machint n) (checked_to_machint LCP.word_size)) a
  | otherwise = error "LC: Unable to shift with an index greater than 32."

checked_to_machint :: Integral a => a -> F.Machint
checked_to_machint x | x >= 0 && x < 2^LCP.word_size = fromIntegral x
checked_to_machint _ = error "checked_machint"

stored_size :: F.Ftyp -> Int
stored_size (F.Fix n) | n <= 2^8 = 8
stored_size (F.Fix n) | n <= 2^16 = 16
stored_size _ = 32

int_const :: Integral n => n -> F.Atom
int_const n = F.Aconst (F.Ointconst (fromIntegral n))

ix_const :: Integral n => n -> F.Atom
ix_const n = F.Aunop (F.Omodix 32) (int_const n)
