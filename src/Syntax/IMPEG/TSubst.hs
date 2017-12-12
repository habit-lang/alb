{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances, GeneralizedNewtypeDeriving #-}
module Syntax.IMPEG.TSubst where

import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Syntax.IMPEG
import Syntax.IMPEG.KSubst (KSubst)
import qualified Syntax.IMPEG.KSubst as K

----------------------------------------------------------------------------------------------------

newtype TSubst id = S (Map id (Type id))
    deriving Show

empty = S (Map.empty)
singleton v t = S (Map.singleton v t)
new pairs = S (foldl (\m (k, v) -> Map.insert k v m) Map.empty pairs)
compose (S m1) (S m2) = S (Map.union m1 m2')
    where m2' = Map.map (S m1 #) m2
isEmpty (S m) = Map.null m
assocs (S m) = Map.assocs m
domain (S m) = Map.keys m

consistent (S m1) (S m2) = all (\v -> Map.lookup v m1 == Map.lookup v m2) vs  -- hyper efficient?
    where vs = intersect (Map.keys m1) (Map.keys m2)

extend          :: Ord id => id -> Type id -> TSubst id -> TSubst id
extend v t (S s) = S (Map.insert v t s)

----------------------------------------------------------------------------------------------------

infixr 6 #
class HasTypeVariables t id | t -> id
    where tvs :: t -> [id]
          (#) :: TSubst id  -> t -> t
          inst :: [Type id] -> t -> t
          gen :: Int -> [id] -> t -> t

instance HasTypeVariables t id => HasTypeVariables (Maybe t) id
    where tvs = maybe [] tvs
          (#) s = fmap (s #)
          inst ts = fmap (inst ts)
          gen i vs = fmap (gen i vs)

instance HasTypeVariables t id => HasTypeVariables (Located t) id
    where tvs (At _ t) = tvs t
          (#) s = fmap (s #)
          inst ts = fmap (inst ts)
          gen i vs = fmap (gen i vs)

instance HasTypeVariables t id => HasTypeVariables [t] id
    where tvs = concatMap tvs
          (#) s = fmap (s #)
          inst ts = fmap (inst ts)
          gen i vs = fmap (gen i vs)

----------------------------------------------------------------------------------------------------

-- Type-like things

instance Ord id => HasTypeVariables (Type id) id
    where tvs (TyCon {})     = []
          tvs (TyVar id)     = [id]
          tvs (TyGen {})     = []
          tvs (TyApp t t')   = tvs t ++ tvs t'
          tvs (TyNat {})     = []
          tvs (TyKinded t _) = tvs t
          tvs (TyLabel {})   = []

          s # t@(TyCon {})   = t
          S m # t@(TyVar id) = case Map.lookup id m of
                                 Nothing -> t
                                 Just t' -> t'
          s # t@(TyGen i)    = t
          s # TyApp t t'     = TyApp (s # t) (s # t')
          s # t@(TyNat {})   = t
          s # TyKinded t k   = TyKinded (s # t) k
          s # t@(TyLabel {}) = t

          inst ts (TyGen i)      = ts !! i
          inst ts (TyApp t t')   = TyApp (inst ts t) (inst ts t')
          inst ts (TyKinded t k) = TyKinded (inst ts t) k
          inst ts t              = t

          gen n vs (TyVar v) =
              case elemIndex v vs of
                Nothing -> TyVar v
                Just i  -> TyGen (n + i)
          gen n vs (TyApp t t')   = TyApp (gen n vs t) (gen n vs t')
          gen n vs (TyKinded t k) = TyKinded (gen n vs t) k
          gen n vs t              = t

instance Ord id => HasTypeVariables (BitdataField id) id
    where tvs (LabeledField _ ty _)            = tvs ty
          tvs _                                = []
          s # LabeledField name ty init        = LabeledField name (s # ty) init
          s # f                                = f
          inst ts (LabeledField name ty init)  = LabeledField name (inst ts ty) init
          inst _ f                             = f
          gen n vs (LabeledField name ty init) = LabeledField name (gen n vs ty) init
          gen _ _  f                           = f

instance Ord id => HasTypeVariables (StructRegion id) id
    where tvs (StructRegion _ tys)            = tvs tys
          s # StructRegion nameInit ty        = StructRegion nameInit (s # ty)
          inst ts (StructRegion nameInit ty)  = StructRegion nameInit (inst ts ty)
          gen n vs (StructRegion nameInit ty) = StructRegion nameInit (gen n vs ty)

instance Ord id => HasTypeVariables (PredType PredFN id) id
    where tvs (PredFN _ ts mt _)        = nub (tvs ts ++ tvs mt)
          s # (PredFN cl ts mt fl)      = PredFN cl (s # ts) (s # mt) fl
          inst ts (PredFN cl ts' mt fl) = PredFN cl (inst ts ts') (inst ts mt) fl
          gen i vs (PredFN cl ts mt fl) = PredFN cl (gen i vs ts) (gen i vs mt) fl

instance Ord id => HasTypeVariables (PredType Pred id) id
    where tvs (Pred _ ts _)        = nub (tvs ts)
          s # (Pred cl ts fl)      = Pred cl (s # ts) fl
          inst ts (Pred cl ts' fl) = Pred cl (inst ts ts') fl
          gen i vs (Pred cl ts fl) = Pred cl (gen i vs ts) fl

instance (Ord id, HasTypeVariables t id, HasTypeVariables p id) => HasTypeVariables (Qual p t) id
    where tvs (ps :=> t)      = nub (tvs ps ++ tvs t)
          s # (ps :=> t)      = (s # ps) :=> (s # t)
          inst ts (ps :=> t)  = inst ts ps :=> inst ts t
          gen i vs (ps :=> t) = gen i vs ps :=> gen i vs t

instance (Ord id, HasTypeVariables (PredType p id) id, HasTypeVariables (Type id) id) => HasTypeVariables (Scheme p id) id
    where -- The definitions of tvs and (#) for Type ignore TyGens; this means that we can afford
          -- to ignore the quantifiers when computing the type variables or or applying a
          -- substitution to a type scheme.
          tvs (Forall ks qt) = tvs qt
          s # Forall ks qt   = Forall ks (s # qt)
          -- On the other hand, we have no way at the moment to represent nested quantification, so
          -- instantiation is a no-op on type schemes.  This might seem a bit odd---one might think
          -- instantiation would be the fundamental operation on type schemes---but the 'inst'
          -- function requires a list of new types, which means that calling it requires having
          -- already deconstructed the Forall.
          inst ts tys        = tys
          gen i vs tys       = tys

----------------------------------------------------------------------------------------------------

-- Q: should knowledge about located stuff spread through unify and match, or is it enough to
-- restrict that to type inference?

type Unifier = (KSubst, TSubst KId)
emptyUnifier = (K.empty, empty)

isEmptyU :: Unifier -> Bool
isEmptyU (ks, s) = K.isEmpty ks && isEmpty s

composeU :: Unifier -> Unifier -> Unifier
composeU (ks, s) (ks', s') = (K.compose ks ks', compose s s')

consistentU :: Unifier -> Unifier -> Bool
consistentU (ks, s) (ks', s') = K.consistent ks ks' && consistent s s'

(##) :: (K.HasKinds t, HasTypeVariables t KId) => Unifier -> t -> t
(ks, s) ## x = s # (ks K.# x)

class (K.HasKinds t, HasTypeVariables t KId) => Unifies t
    where unify :: ([KId], [Id]) -> t -> t -> Either UnificationFailure Unifier
          -- match only binds variables on its rhs
          match :: ([KId], [Id]) -> t -> t -> Either UnificationFailure Unifier

data UnificationMode = Match | Unify
data UnificationFailure = TypesFail UnificationMode (Type KId) (Type KId)
                        | PredsFail UnificationMode (PredType Pred KId) (PredType Pred KId)
                        | OccursCheck KId (Type KId)
                        | KindsDontMatch Kind Kind
                        | TypeNotGeneral
                        | StructuralFail
                        | QualFail

-- instance Error UnificationFailure
--     where noMsg = StructuralFail
--           strMsg _ = StructuralFail

typesFail m a b     = Left (TypesFail m a b)
predsFail m a b     = Left (PredsFail m a b)
occursCheck v t     = Left (OccursCheck v t)
kindsDontMatch k k' = Left (KindsDontMatch k k')
typeNotGeneral      = Left TypeNotGeneral

instance Unifies t => Unifies (Located t)
    where unify gvars (At _ t) (At _ t') = unify gvars t t'
          match gvars (At _ t) (At _ t') = match gvars t t'

instance Unifies t => Unifies (Maybe t)
    where unify _ Nothing Nothing       = return emptyUnifier
          unify gvars (Just t) (Just u) = unify gvars t u
          unify _ _ _                   = Left StructuralFail

          match _ Nothing Nothing       = return emptyUnifier
          match gvars (Just t) (Just u) = match gvars t u
          match _ _ _                   = Left StructuralFail

instance Unifies t => Unifies [t]
    where unify _ [] []             = return emptyUnifier
          unify gvars (t:ts) (u:us) = do u <- unify gvars t u
                                         u' <- unify gvars (u ## ts) (u ## us)
                                         return (composeU u' u)
          unify _ _ _               = Left StructuralFail

          match _ [] []             = return emptyUnifier
          match gvars (t:ts) (u:us) = do u <- match gvars t u
                                         u' <- match gvars ts us
                                         if (consistentU u u')
                                           then (return (composeU u' u)) 
                                           else Left StructuralFail
          match _ _ _               = Left StructuralFail

varBind :: ([KId], [Id]) -> KId -> Type KId -> Either UnificationFailure Unifier
varBind (_, gkvs) (Kinded name k) (TyVar (Kinded name' k'))
    | name == name' = case K.unify gkvs k k' of
                        Left _   -> kindsDontMatch k k'
                        Right ks -> return (ks, empty)
varBind (gtvs, gkvs) v@(Kinded name k) t
    | v `elem` gtvs            = typeNotGeneral
    | v `elem` tvs t           = occursCheck v t
    | otherwise                = case K.unify gkvs k (kindOf t) of
                                   Left _   -> kindsDontMatch k (kindOf t)
                                   Right ks -> return (ks, singleton v t)

kindOfGen :: [KId] -> Type KId -> Kind
kindOfGen _ (TyCon (Kinded _ k))  = k
kindOfGen _ (TyVar (Kinded _ k))  = k
kindOfGen ks (TyGen i)            = if i < length ks then kind (ks !! i) else error "Syntax.IMPEG.TSubst:173"
kindOfGen ks (TyApp (At _ t) _) =
    case kindOfGen ks t of
      KFun _ result -> result
      _             -> error "Syntxax.IMPEG.TSubst:177"
kindOfGen _ (TyNat _)             = KNat
kindOfGen _ (TyKinded _ (At _ k)) = k
kindOfGen _ (TyLabel _)           = KLabel

kindOf :: Type KId -> Kind
kindOf = kindOfGen []

instance Unifies (Type KId)
    where unify gvars (TyApp t u) (TyApp t' u') =
              do s <- unify gvars t t'
                 s' <- unify gvars (s ## u) (s ## u')
                 return (composeU s' s)
          unify _ (TyCon s) (TyCon s')
              | s == s'           = return emptyUnifier
          unify gvars@(gtvs,_) t@(TyVar v) t'@(TyVar v')
              | v' `elem` gtvs    = varBind gvars v t'
          unify gvars t (TyVar v) = varBind gvars v t
          unify gvars (TyVar v) t = varBind gvars v t
          unify _ (TyNat n) (TyNat m)
              | n == m            = return emptyUnifier
          unify _ (TyLabel l) (TyLabel l')
              | l == l'           = return emptyUnifier
          unify _ t u             = typesFail Unify t u

          match gvars (TyApp t u) (TyApp t' u') =
              do s <- match gvars t t'
                 s' <- match gvars u u'
                 if (consistentU s s')
                   then (return (composeU s' s))
                   else (return emptyUnifier)
          match _ (TyCon s) (TyCon s')     | s == s' = return emptyUnifier
          match gvars t (TyVar v)                    = varBind gvars v t
          match _ (TyNat n) (TyNat m)      | n == m  = return emptyUnifier
          match _ (TyLabel l) (TyLabel l') | l == l' = return emptyUnifier
          match _ t u                                = typesFail Match t u

instance Unifies (PredType Pred KId)
    where unify gvars p@(Pred className ts fl) q@(Pred className' ts' fl')
              | className /= className' || fl /= fl' = predsFail Unify p q
              | otherwise = unify gvars ts ts'
          match gvars p@(Pred className ts fl) q@(Pred className' ts' fl')
              | className /= className' || fl /= fl' = predsFail Match p q
              | otherwise = match gvars ts ts'

instance (Unifies p, Unifies t) => Unifies (Qual p t)
    where unify gvars (ps :=> t) (ps' :=> t') =
              do s <- unify gvars ps ps'
                 s' <- unify gvars (s ## t) (s ## t')
                 if (consistentU s s')
                   then (return (composeU s' s))
                   else (Left QualFail)
          match gvars (ps :=> t) (ps' :=> t') =
              do s <- match gvars ps ps'
                 s' <- match gvars t t'
                 if (consistentU s s')
                   then (return (composeU s' s))
                   else (Left QualFail)


