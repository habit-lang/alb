{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, UndecidableInstances, DeriveDataTypeable, StandaloneDeriving, TemplateHaskell, ScopedTypeVariables #-}
module Syntax.IMPEG (module Syntax.Common, module Syntax.IMPEG) where

import Language.Haskell.TH hiding (Match, Type, Guard, Kind)
import Data.Generics hiding (Fixity)
import Data.List
import Syntax.Common

--------------------------------------------------------------------------------
-- Kinds and types
--------------------------------------------------------------------------------

data Type id = TyCon id
             | TyVar id
             | TyGen Int -- quantified type variable
             | TyApp !(Located (Type id)) !(Located (Type id))
             | TyNat Integer
             | TyKinded (Located (Type id)) (Located Kind)
             | TyLabel Id
               deriving (Eq, Show, Typeable, Data)

flattenType :: Located (Type id) -> (Located (Type id), [Located (Type id)])
flattenType (At _ (TyApp lhs rhs)) = (op, ts ++ [rhs])
    where (op, ts) = flattenType lhs
flattenType t = (t, [])

--------------------------------------------------------------------------------
-- Predicates and qualifiers
--------------------------------------------------------------------------------

type PredType pred tyid = pred (Located (Type tyid))
data Qual p t           = [Located p] :=> Located t
  deriving (Eq, Typeable, Data)
data Scheme p tyid      = Forall [tyid] (Qual (PredType p tyid) (Type tyid))

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

data Expr p tyid = ELet (Decls p tyid) (Located (Expr p tyid))
                 | ELam Id (Located (Expr p tyid))
                 | EVar Id
                 | ECon Id
                 | EBitCon Id [(Id, Located (Expr p tyid))]
                 | EBits Integer Int
                 | EMatch (Match p tyid)
                 | EApp (Located (Expr p tyid)) (Located (Expr p tyid))
                 | EBind Id (Located (Expr p tyid)) (Located (Expr p tyid))
                 | EStructInit Id [(Located Id, Located (Expr p tyid))]

flattenApp :: Located (Expr p t) -> (Located (Expr p t), [Located (Expr p t)])
flattenApp (At _ (EApp lhs rhs)) = (op, es ++ [rhs])
    where (op, es) = flattenApp lhs
flattenApp t = (t, [])

flattenLambda :: Expr p t -> ([Id], Expr p t)
flattenLambda (ELam v (At _ e)) = (v:vs, body)
    where (vs, body) = flattenLambda e
flattenLambda e = ([], e)

flattenDo :: Expr p t -> ([(Id, Expr p t)], Expr p t)
flattenDo (EBind v (At _ e) (At _ e')) = ((v, e) : binds, result)
    where (binds, result) = flattenDo e'
flattenDo e = ([], e)

replacement m id = case lookup id m of
                     Nothing  -> id
                     Just id' -> id'

instance HasVariables (Expr p t)
    where freeVariables (ELet ds body) =
              freeVariables ds ++ withoutBound ds (freeVariables body)
          freeVariables (ELam v body) =
              filter (v /=) (freeVariables body)
          freeVariables (EVar id) = [id]
          freeVariables (ECon id) = []
          freeVariables (EBitCon _ es) = concatMap (freeVariables . snd) es
          freeVariables (EBits {}) = []
          freeVariables (EMatch m) = freeVariables m
          freeVariables (EApp e e') =
              freeVariables e ++ freeVariables e'
          freeVariables (EBind var e rest) =
              freeVariables e ++ filter (var /=) (freeVariables rest)
          freeVariables (EStructInit _ fields) =
              concatMap (freeVariables . snd) fields

          rename m (ELet ds e)         = ELet (rename m ds) (rename m e)
          rename m (ELam v e)          = ELam (replacement m v) (rename m e)
          rename m (EVar id)           = EVar (replacement m id)
          rename m (ECon id)           = ECon id
          rename m (EBitCon id fs)     = EBitCon id [(f, rename m e) | (f,e) <- fs]
          rename m l@(EBits {})        = l
          rename m (EMatch match)      = EMatch (rename m match)
          rename m (EApp e e')         = EApp (rename m e) (rename m e')
          rename m (EBind v e e')      = EBind (replacement m v) (rename m e) (rename m e')
          rename m (EStructInit id fs) = EStructInit id [(f, rename m e) | (f,e) <- fs]

--------------------------------------------------------------------------------
-- Matches
--------------------------------------------------------------------------------

data Match p tyid = MFail                                   -- "fail"            match failure
                  | MCommit (Located (Expr p tyid))         -- "^ e"             commit result
                  | MElse (Match p tyid) (Match p tyid)     -- "m1 | m2"         alternative
                  | MGuarded (Guard p tyid) (Match p tyid)  -- "g => m"          guarded matches

instance HasVariables (Match p t)
    where freeVariables MFail          = []
          freeVariables (MCommit e)    = freeVariables e
          freeVariables (MElse m m')   = freeVariables m ++ freeVariables m'
          freeVariables (MGuarded g m) = freeVariables g ++ withoutBound g (freeVariables m)

          rename m MFail                = MFail
          rename m (MCommit e)          = MCommit (rename m e)
          rename m (MElse match match') = MElse (rename m match) (rename m match')
          rename m (MGuarded g match)   = MGuarded (rename m g) (rename m match)

flattenElses :: Match p t -> [Match p t]
flattenElses (MElse m n) = ms ++ ns
    where ms = flattenElses m
          ns = flattenElses n
flattenElses m = [m]

flattenGuards :: Match p t -> ([Guard p t], Match p t)
flattenGuards (MGuarded g m) = (g:guards, result)
    where (guards, result) = flattenGuards m
flattenGuards m = ([], m)

data Guard p tyid = GFrom (Located (Pattern p tyid)) (Located (Expr p tyid))
                  | GLet (Decls p tyid)

instance Binder (Guard p t)
    where bound (GFrom p _) = bound p
          bound (GLet ds)   = bound ds

instance HasVariables (Guard p t)
    where freeVariables (GFrom p e) = freeVariables p ++ freeVariables e
          freeVariables (GLet ds)   = freeVariables ds

          rename m (GFrom p e) = GFrom (rename m p) (rename m e)
          rename m (GLet ds)   = GLet (rename m ds)

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

data Pattern p tyid = PWild
                    | PVar Id
                    | PCon Id [Id]
                    | PTyped (Located (Pattern p tyid)) (Scheme p tyid)
                    | PGuarded (Pattern p tyid) (Guard p tyid)

instance Binder (Pattern p t)
    where bound PWild          = []
          bound (PVar id)      = [id]
          bound (PCon _ ids)   = ids
          bound (PTyped p _)   = bound p
          bound (PGuarded p g) = bound p ++ bound g

instance HasVariables (Pattern p t)
    where freeVariables PWild          = []
          freeVariables (PVar {})      = []
          freeVariables (PCon {})      = []
          freeVariables (PTyped p _)   = freeVariables p
          freeVariables (PGuarded p g) = freeVariables p ++ freeVariables g

          rename m PWild            = PWild
          rename m (PVar id)        = PVar (replacement m id)
          rename m (PCon cname ids) = PCon cname (map (replacement m) ids)
          rename m (PTyped p tys)   = PTyped (rename m p) tys
          rename m (PGuarded p g)   = PGuarded (rename m p) (rename m g)

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

data Signature p tyid = Signature Id (KScheme (Scheme p tyid))

type Function p tyid = (Id, [Id], Match p tyid)
type Functions p tyid = [Function p tyid]

data TypingGroup p tyid = Explicit (Function p tyid) (KScheme (Scheme p tyid))
                        | Implicit (Functions p tyid)
                        | Pattern { pattern    :: Located (Pattern p tyid)
                                  , body       :: Match p tyid
                                  , signatures :: [Signature p tyid] }
                        | PrimValue (Signature p tyid) String

instance Binder (TypingGroup p t)
    where bound (Explicit (name, _, _) _) = [name]
          bound (Implicit fcns)           = [id | (id, _, _) <- fcns]
          bound (Pattern p _ _)           = bound p

instance HasVariables (TypingGroup p t)
    where freeVariables (Explicit (name, params, body) _) = freeVariables body \\ (name : params)
          freeVariables (Implicit fcns)                   = nub (concat freeVars) \\ names
              where (names, freeVars) = unzip [(name, freeVariables body \\ params) | (name, params, body) <- fcns]
          freeVariables (Pattern _ e _)                   = freeVariables e

          rename m (Explicit (name, params, body) tys) = Explicit (replacement m name, map (replacement m) params, rename m body) tys
          rename m (Implicit fs)                       = Implicit [(replacement m name, map (replacement m) params, rename m body) | (name, params, body) <- fs]
          rename m (Pattern p e ss)                    = Pattern (rename m p) (rename m e) [Signature (replacement m id) tys | Signature id tys <- ss]

data Decls p tyid = Decls { groups :: [TypingGroup p tyid] } -- sorted by dependencies

appendDecls        :: Decls p tyid -> Decls p tyid -> Decls p tyid
appendDecls ds1 ds2 = Decls (groups ds1 ++ groups ds2)

concatDecls           :: [Decls p tyid] -> Decls p tyid
concatDecls []         = Decls []
concatDecls (ds : dss) = appendDecls ds (concatDecls dss)

instance Binder (Decls p t)
    where bound (Decls bs) = concatMap bound bs

instance HasVariables (Decls p t)
    where freeVariables (Decls [])       = []
          freeVariables (Decls (b : bs)) = freeVariables b ++ withoutBound b (freeVariables (Decls bs))

          rename m (Decls gs) = Decls (rename m gs)

emptyDecls = Decls []

--------------------------------------------------------------------------------
-- Top level declarations
--------------------------------------------------------------------------------

paramName :: Either (Kinded Id) Id -> Id
paramName (Left (Kinded name _)) = name
paramName (Right name)           = name

data TopDecl p tyid typaram = Datatype tyid [Located typaram] [Ctor tyid (PredType p tyid) (Type tyid)] [Id]
                            | Bitdatatype Id (Maybe (Scheme p tyid)) [Ctor tyid (PredType p tyid) (BitdataField tyid)] [Id]
                            | Struct Id (Maybe (Scheme p tyid)) (Ctor tyid (PredType p tyid) (StructRegion tyid)) [Id]
                            | Area Bool [(Located Id, Id)] (Scheme p tyid)
                            | Class Id [Located typaram] [Located ClassConstraint] [Signature p tyid] (Functions p tyid)
                            | Instance Id Id [(Qual (PredType p tyid) (PredType p tyid), Functions p tyid)]
                            | Require [(Id, Located (PredType p tyid))] [Located (PredType p tyid)]

data ClassConstraint = Fundep (Fundep Int) | Opaque Int
  deriving (Eq, Show, Typeable, Data)
data BitdataField tyid = LabeledField Id (Located (Type tyid)) (Maybe Id)
                       | ConstantField (Located Literal)
  deriving (Eq, Show, Typeable, Data)
data StructRegion tyid = StructRegion (Maybe StructField) (Located (Type tyid))
  deriving (Eq, Show, Typeable, Data)
data StructField = StructField (Located Id) (Maybe Id)
  deriving (Eq, Show, Typeable, Data)

type TopDecls p tyid typaram = [Located (TopDecl p tyid typaram)]

data Primitive p tyid = PrimType tyid Kind
                      | PrimClass Id [Located (Kinded Id)] [Located (Fundep Int)] [Signature p tyid]
                      | PrimCon (Signature p tyid) String

type Primitives p tyid = [Located (Primitive p tyid)]

--------------------------------------------------------------------------------
-- Programs
--------------------------------------------------------------------------------

data Program p tyid typaram = Program { decls      :: Decls p tyid
                                      , topDecls   :: TopDecls p tyid typaram
                                      , primitives :: Primitives p tyid }

emptyProgram = Program { decls      = emptyDecls
                       , topDecls   = []
                       , primitives = [] }

--------------------------------------------------------------------------------
-- Data and Typeable instances
--
-- In earlier versions of GHC, these had to be separately defined because GHC's
-- 'deriving' facility doesn't work with complex kinds.  Versions of GHC >= 7.8,
-- however, don't allow manual instance of Typeable.
--------------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ >= 708

deriving instance Typeable Scheme
deriving instance Typeable Expr
deriving instance Typeable Match
deriving instance Typeable Guard
deriving instance Typeable Pattern
deriving instance Typeable Signature
deriving instance Typeable Decls
deriving instance Typeable Primitive
deriving instance Typeable TypingGroup
deriving instance Typeable TopDecl
deriving instance Typeable Program

#else

#define INSTANCE_TYPEABLE_P(tycon,str) \
instance (Typeable1 p, Typeable tyid) => Typeable (tycon p tyid) where \
  typeOf (_ :: tycon p tyid) = mkTyConApp (mkTyCon str) [typeOf1 (undefined :: p ()), typeOf (undefined :: tyid)]

#define INSTANCE_TYPEABLE_P2(tycon,str) \
instance (Typeable1 p, Typeable tyid, Typeable typaram) => Typeable (tycon p tyid typaram) where \
  typeOf (_ :: tycon p tyid typaram) = mkTyConApp (mkTyCon str) [typeOf1 (undefined :: p ()), typeOf (undefined :: tyid), typeOf (undefined :: typaram)]

INSTANCE_TYPEABLE_P(Scheme,"Scheme")
INSTANCE_TYPEABLE_P(Expr,"Expr")
INSTANCE_TYPEABLE_P(Match,"Match")
INSTANCE_TYPEABLE_P(Guard,"Guard")
INSTANCE_TYPEABLE_P(Pattern,"Pattern")
INSTANCE_TYPEABLE_P(Signature,"Signature")
INSTANCE_TYPEABLE_P(Decls,"Decls")
INSTANCE_TYPEABLE_P(Primitive,"Primitive")
INSTANCE_TYPEABLE_P(TypingGroup,"TypingGroup")
INSTANCE_TYPEABLE_P2(TopDecl,"TopDecl")
INSTANCE_TYPEABLE_P2(Program,"Program")

#endif

instance (Typeable1 p, Data (p (Located (Type tyid))), Data tyid, Data typaram) =>
         Data (TopDecl p tyid typaram) where
  gfoldl k z (Datatype x1 x2 x3 x4) = z Datatype `k` x1 `k` x2 `k` x3 `k` x4
  gfoldl k z (Bitdatatype x1 x2 x3 x4) = z Bitdatatype `k` x1 `k` x2 `k` x3 `k` x4
  gfoldl k z (Struct x1 x2 x3 x4) = z Struct `k` x1 `k` x2 `k` x3 `k` x4
  gfoldl k z (Area x1 x2 x3) = z Area `k` x1 `k` x2 `k` x3
  gfoldl k z (Class x1 x2 x3 x4 x5) = z Class `k` x1 `k` x2 `k` x3 `k` x4 `k` x5
  gfoldl k z (Instance x1 x2 x3) = z Instance `k` x1 `k` x2 `k` x3
  gfoldl k z (Require x1 x2) = z Require `k` x1 `k` x2


instance (Typeable1 p, Data (p (Located (Type tyid))), Data tyid, Data typaram) =>
         Data (Program p tyid typaram) where
  gfoldl k z (Program x1 x2 x3) = z Program `k` x1 `k` x2 `k` x3



-- Rather than manually defining these instances, we use Template Haskell to do it for us.

#if defined(MIN_VERSION_GLASGOW_HASKELL) && MIN_VERSION_GLASGOW_HASKELL(8,2,1,0)

$(let types = [''Scheme, ''Decls, ''Primitive, ''Signature, ''TypingGroup, ''Pattern, ''Match, ''Guard, ''Expr]
      mkClause k z (RecC name args) = mkClause k z (NormalC name (map undefined args))
      mkClause k z (NormalC name args) = do
        args' <- mapM (newName . const "y") args
        let body :: ExpQ
            body = foldl (\c x -> varE k `appE` c `appE` varE x) (appE (varE z) (conE name)) args'
        match (conP name (map varP args')) (normalB body) []
      mkInstance x = do
               TyConI dec <- reify x
               case dec of
                 DataD [] name typarams _ cons _  ->
                   [d|instance (Typeable1 p, Data (p (Located (Type tyid))), Data tyid) => Data ($(conT name) p tyid) where gfoldl k z x = $(caseE (varE 'x) (map (mkClause 'k 'z) cons)) |]
  in (return . concat) =<< mapM mkInstance types)

#else

$(let types = [''Scheme, ''Decls, ''Primitive, ''Signature, ''TypingGroup, ''Pattern, ''Match, ''Guard, ''Expr]
      mkClause k z (RecC name args) = mkClause k z (NormalC name (map undefined args))
      mkClause k z (NormalC name args) = do
        args' <- mapM (newName . const "y") args
        let body :: ExpQ
            body = foldl (\c x -> varE k `appE` c `appE` varE x) (appE (varE z) (conE name)) args'
        match (conP name (map varP args')) (normalB body) []
      mkInstance x = do
               TyConI dec <- reify x
               case dec of
                 DataD [] name typarams cons _ ->
                   [d|instance (Typeable1 p, Data (p (Located (Type tyid))), Data tyid) => Data ($(conT name) p tyid) where gfoldl k z x = $(caseE (varE 'x) (map (mkClause 'k 'z) cons)) |]
  in (return . concat) =<< mapM mkInstance types)

#endif
