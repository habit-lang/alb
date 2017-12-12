{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, UndecidableInstances #-}
module Syntax.IMPEG.KSubst where

import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Printer.Common hiding (empty)
import Syntax.Common
import Syntax.IMPEG

--------------------------------------------------------------------------------

newtype KSubst = S (Map Id Kind) deriving Show

empty = S (Map.empty)
singleton v k = S (Map.singleton v k)
new pairs = S (foldl (\m (k, v) -> Map.insert k v m) Map.empty pairs)
compose (S m1) (S m2) = S (Map.union m1 m2')
    where m2' = Map.map (S m1 #) m2
isEmpty (S m) = Map.null m

consistent (S m1) (S m2) = all (\v -> Map.lookup v m1 == Map.lookup v m2) vs  -- hyper efficient?
    where vs = intersect (Map.keys m1) (Map.keys m2)

infixr 6 #
class HasKinds t
    where vars :: t -> [Id]
          (#) :: KSubst -> t -> t

instance HasKinds t => HasKinds (Maybe t)
    where vars Nothing  = []
          vars (Just x) = vars x
          (#) s         = fmap (s #)

instance HasKinds t => HasKinds (Located t)
    where vars (At _ x) = vars x
          (#) s         = fmap (s #)

instance (HasKinds t, HasKinds u) => HasKinds (t, u)
    where vars (a, b) = nub (vars a ++ vars b)
          s # (a, b)  = (s # a, s # b)

instance (HasKinds t, HasKinds u) => HasKinds (Either t u)
    where vars (Left x) = vars x
          vars (Right x) = vars x

          s # Left x  = Left (s # x)
          s # Right x = Right (s # x)

instance HasKinds t => HasKinds [t]
    where vars  = nub . concatMap vars
          (#) s = map (s #)

----------------------------------------------------------------------------------------------------

instance HasKinds Kind
    where vars (KVar v)    = [v]
          vars (KFun k k') = nub (vars k ++ vars k')
          vars _           = []

          (S m) # KVar v  = fromMaybe (KVar v) (Map.lookup v m)
          s # (KFun k k') = KFun (s # k) (s # k')
          s # k           = k

instance HasKinds (Kinded t)
    where vars (Kinded _ k) = vars k
          s # (Kinded t k)  = Kinded t (s # k)

instance HasKinds t => HasKinds (KScheme t)
    where vars (ForallK ids x) = filter (`notElem` ids) (vars x)
          S m # ForallK ids x  = ForallK ids (S (Map.filterWithKey (\id _ -> id `notElem` ids) m) # x)

----------------------------------------------------------------------------------------------------

instance HasKinds Id
    where vars _ = []
          s # id = id

instance HasKinds tyid => HasKinds (Type tyid)
    where vars (TyCon id)     = vars id
          vars (TyVar id)     = vars id
          vars (TyGen _)      = []
          vars (TyApp t t')   = vars [t, t']
          vars (TyNat _)      = []
          vars (TyKinded t k) = nub (vars t ++ vars k)
          vars (TyLabel _)    = []

          s # TyCon id     = TyCon (s # id)
          s # TyVar id     = TyVar (s # id)
          s # TyGen i      = TyGen i
          s # TyApp t t'   = TyApp (s # t) (s # t')
          s # TyNat i      = TyNat i
          s # TyKinded t k = TyKinded (s # t) (s # k)
          s # TyLabel l    = TyLabel l

instance HasKinds tyid => HasKinds (PredFN tyid)
    where vars (PredFN _ ts mt _)         = nub (vars ts ++ vars mt)
          s # PredFN className ts mt flag = PredFN className (map (s #) ts) (s # mt) flag

instance HasKinds tyid => HasKinds (Pred tyid)
    where vars (Pred _ ts _)         = vars ts
          s # Pred className ts flag = Pred className (map (s #) ts) flag

instance (HasKinds p, HasKinds t) => HasKinds (Qual p t)
    where vars (ps :=> t) = nub (vars ps ++ vars t)
          s # (ps :=> t)  = (s # ps) :=> (s # t)

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Scheme p tyid)
    where vars (Forall ks qt) = nub (vars ks ++ vars qt)
          s # Forall ks qt    = Forall (s # ks) (s # qt)

----------------------------------------------------------------------------------------------------

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Decls p tyid)
    where vars (Decls ds) = vars ds
          s # Decls ds    = Decls (s # ds)

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Signature p tyid)
    where vars (Signature _ qty)   = vars qty
          s # (Signature name qty) = Signature name (s # qty)

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (TypingGroup p tyid)
    where vars (Explicit f tys) = nub (vars f ++ vars tys)
          vars (Implicit fs)    = vars fs
          vars (Pattern p b ss) = nub (vars p ++ vars b ++ vars ss)
          vars (PrimValue s _)  = vars s

          s # Explicit f tys = Explicit (s # f) (s # tys)
          s # Implicit fs    = Implicit (s # fs)
          s # Pattern p b ss = Pattern (s # p) (s # b) (s # ss)
          s # PrimValue signature name = PrimValue (s # signature) name

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Id, [Id], (Match p tyid))
    where vars (_, _, body)        = vars body
          s # (name, params, body) = (name, params, s # body)

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Expr p tyid)
    where vars (ELet ds e)        = nub (vars ds ++ vars e)
          vars (ELam v e)         = vars e
          vars (EMatch m)         = vars m
          vars (EApp e e')        = vars [e, e']
          vars (EBind v e e')     = vars [e, e']
          vars (EStructInit n fs) = nub (concat [vars e | (_, e) <- fs])

          s # ELet ds e        = ELet (s # ds) (s # e)
          s # ELam v e         = ELam v (s # e)
          s # EMatch m         = EMatch (s # m)
          s # EApp e e'        = EApp (s # e) (s # e')
          s # EBind v e e'     = EBind v (s # e) (s # e')
          s # EStructInit n fs = EStructInit n [(v, s # e) | (v, e) <- fs]
          s # e                = e

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Match p tyid)
    where vars MFail          = []
          vars (MCommit e)    = vars e
          vars (MElse e e')   = vars [e, e']
          vars (MGuarded g m) = nub (vars g ++ vars m)

          s # MFail        = MFail
          s # MCommit e    = MCommit (s # e)
          s # MElse m m'   = MElse (s # m) (s # m')
          s # MGuarded g m = MGuarded (s # g) (s # m)

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Guard p tyid)
    where vars (GFrom p e) = nub (vars p ++ vars e)
          vars (GLet ds)   = vars ds

          s # GFrom p e = GFrom (s # p) (s # e)
          s # GLet ds   = GLet (s # ds)

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Pattern p tyid)
    where vars (PTyped p tys) = nub (vars p ++ vars tys)
          vars (PGuarded p g) = nub (vars p ++ vars g)
          vars _              = []

          s # PTyped p tys = PTyped (s # p) (s # tys)
          s # PGuarded p g = PGuarded (s # p) (s # g)
          s # p            = p

----------------------------------------------------------------------------------------------------

instance (HasKinds tyid, HasKinds typaram, HasKinds (PredType p tyid)) => HasKinds (TopDecl p tyid typaram)
    where vars (Datatype name params ctors _) = nub (vars name ++ vars params ++ vars ctors)
          vars (Bitdatatype _ size ctors _)   = nub (vars size ++ vars ctors)
          vars (Struct _ size regions _)      = nub (vars size ++ vars regions)
          vars (Area _ _ ty)                  = vars ty
          vars (Class _ params constraints methods defaults) =
              nub (vars params ++ vars methods ++ vars defaults)
          vars (Instance _ _ chain)           = vars chain
          vars (Require ps qs)                = nub (vars ps ++ vars qs)

          s # Datatype name params ctors drv  = Datatype (s # name) (s # params) (s # ctors) drv
          s # Bitdatatype name size ctors drv = Bitdatatype name (s # size) (s # ctors) drv
          s # Struct name size regions drv    = Struct name (s # size) (s # regions) drv
          s # Area v inits ty                 = Area v inits (s # ty)
          s # Class name params constraints methods defaults =
              Class name (s # params) constraints (s # methods) (map (s #) defaults)
          s # Instance name className chain   = Instance name className [ (s # head, map (s #) body) | (head, body) <- chain ]
          s # Require ps qs                   = Require (s # ps) (s # qs)

instance (HasKinds tyid, HasKinds p, HasKinds t) => HasKinds (Ctor tyid p t)
    where vars (Ctor _ quant ps ts)   = nub (vars quant ++ vars ps ++ vars ts)
          s # (Ctor name quant ps ts) = Ctor name (s # quant) (s # ps) (s # ts)

instance HasKinds tyid => HasKinds (BitdataField tyid)
    where vars (LabeledField _ ty _) = vars ty
          vars _                     = []

          s # LabeledField name ty init = LabeledField name (s # ty) init
          s # ConstantField lit         = ConstantField lit

instance HasKinds tyid => HasKinds (StructRegion tyid)
    where vars (StructRegion _ ty)  = vars ty
          s # StructRegion field ty = StructRegion field (s # ty)

----------------------------------------------------------------------------------------------------

instance (HasKinds tyid, HasKinds (PredType p tyid)) => HasKinds (Primitive p tyid)
    where vars (PrimType name k)              = nub (vars name ++ vars k)
          vars (PrimClass _ params _ methods) = nub (vars params ++ vars methods)

          s # PrimType name k = PrimType (s # name) (s # k)
          s # PrimClass name params constraints methods = PrimClass name (map (s #) params) constraints (map (s #) methods)

----------------------------------------------------------------------------------------------------

unify :: [Id] -> Kind -> Kind -> Either String KSubst

unify gvs (KFun k0 k1) (KFun k0' k1') =
    do s <- unify gvs k0 k0'
       s' <- unify gvs (s # k1) (s # k1')
       return (compose s' s)
unify gvs k@(KVar v) k'@(KVar w)
    | v == w          = return empty
    | v `notElem` gvs = return (singleton v k')
    | w `notElem` gvs = return (singleton w k)
    | otherwise       = notGeneral
unify gvs (KVar v) k
    | v `elem` vars k = occursCheck v k
    | v `elem` gvs    = notGeneral
    | otherwise       = return (singleton v k)
unify gvs k (KVar v)
    | v `elem` vars k = occursCheck v k
    | v `elem` gvs    = notGeneral
    | otherwise       = return (singleton v k)
unify gvs k k'
    | k == k'         = return empty
    | otherwise       = cannotUnify k k'

cannotUnify a b = Left ("Cannot unify \"" ++ show (ppr a) ++ "\" with \"" ++ show (ppr b) ++ "\"")
occursCheck v k = Left ("Cannot construct the infinite type " ++ show (ppr v) ++ " = " ++ show (ppr k))
notGeneral      = Left "Kind was not as general as expected"
