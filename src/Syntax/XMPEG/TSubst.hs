{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances #-}
module Syntax.XMPEG.TSubst where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Syntax.Common
import qualified Syntax.IMPEG.TSubst as I
import Syntax.XMPEG

----------------------------------------------------------------------------------------------------

newtype TSubst = S (Map KId Type)
empty = S (Map.empty)
singleton v t = S (Map.singleton v t)
new pairs = S (foldl (\m (k, v) -> Map.insert k v m) Map.empty pairs)
compose (S m1) (S m2) = S (Map.union m1 m2')
    where m2' = Map.map (S m1 #) m2
isEmpty (S m) = Map.null m
assocs (S m) = Map.assocs m
extend v t (S s) = S (Map.insert v t s)
domain (S m) = Map.keys m

under :: [(KId, Type)] -> TSubst -> Maybe [(KId, Type)]
under bs s = concat `fmap` mapM under' bs
    where under' (v, t) = assocs `fmap` unify (s # TyVar v) (s # t)

instance Convertable (I.TSubst KId) TSubst
    where convert (I.S m) = S (Map.map convert m)

instance Convertable I.Unifier TSubst
    where convert (_, s) = convert s

----------------------------------------------------------------------------------------------------

class HasTypeVariables t
    where tvs  :: t -> [KId]
          (#)  :: TSubst -> t -> t

          tvs _ = error "Unimplemented"

class HasTypeVariables t => Quantifiable t
    where inst :: [Type] -> t -> t
          gen  :: Int -> [KId] -> t -> t

class HasTypeVariables t => HasEvidenceVariables t
    where fevs :: t -> [Id]

----------------------------------------------------------------------------------------------------

instance HasTypeVariables t => HasTypeVariables (Maybe t)
    where tvs   = maybe [] tvs
          (#) s = fmap (s #)

instance Quantifiable t => Quantifiable (Maybe t)
    where inst ts = fmap (inst ts)
          gen n vs = fmap (gen n vs)

instance HasEvidenceVariables t => HasEvidenceVariables (Maybe t)
    where fevs = maybe [] fevs

instance HasTypeVariables t => HasTypeVariables [t]
    where tvs   = concatMap tvs
          (#) s = fmap (s #)

instance Quantifiable t => Quantifiable [t]
    where inst ts = fmap (inst ts)
          gen n vs = fmap (gen n vs)

instance HasEvidenceVariables t => HasEvidenceVariables [t]
    where fevs = concatMap fevs

----------------------------------------------------------------------------------------------------

instance HasTypeVariables Type
    where tvs (TyVar id)   = [id]
          tvs (TyApp t t') = nub (tvs t ++ tvs t')
          tvs t            = []

          s@(S m) # TyVar id =
              case Map.lookup id m of
                Nothing -> TyVar id
                Just t' -> s # t'
          _ # TyCon id   = TyCon id
          _ # TyGen i    = TyGen i
          s # TyApp t t' = TyApp (s # t) (s # t')
          _ # TyNat i    = TyNat i
          _ # TyLabel l  = TyLabel l

instance Quantifiable Type
    where inst ts (TyGen i)    = ts !! i
          inst ts (TyApp t t') = TyApp (inst ts t) (inst ts t')
          inst _ t             = t

          gen n vs (TyVar v) =
              case elemIndex v vs of
                Nothing -> TyVar v
                Just i  -> TyGen (n + i)
          gen n vs (TyApp t t')   = TyApp (gen n vs t) (gen n vs t')
          gen n vs t              = t

instance HasTypeVariables (Pred Type)
    where tvs (Pred _ ts _)  = tvs ts
          s # Pred cl ts f   = Pred cl (s # ts) f

instance Quantifiable (Pred Type)
    where inst vs (Pred cl ts f) = Pred cl (inst vs ts) f
          gen n vs (Pred cl ts f) = Pred cl (gen n vs ts) f

instance HasTypeVariables t => HasTypeVariables (Scheme t)
    where s # Forall ks ev t     = Forall ks (s # ev) (s # t)

-- No instance of quantifiable for schemes; this precludes the possiblity of nested quantification.

----------------------------------------------------------------------------------------------------

instance HasTypeVariables Expr
    where s # e@(ELamVar {}) = e
          s # ELetVar tapp   = ELetVar (s # tapp)
          s # e@(EBits {})   = e
          s # ECon tapp      = ECon (s # tapp)
          s # EBitCon i fields = EBitCon i (map substField fields)
              where substField (f, e) = (f, s # e)
          s # ELam v t e     = ELam v (s # t) (s # e)
          s # ELet ds e      = ELet (s # ds) (s # e)
          s # ELetTypes (Left cs) e =
              ELetTypes (Left (catMaybes [do cond' <- cond `under` s; impr' <- impr `under` s; return (cond', impr') | (cond, impr) <- cs]))
                        (s # e)
          s # (ELetTypes (Right (args, results, f)) e) =
              ELetTypes (Right (args, results, (s #) . f)) (s # e)
          s # ESubst exprSubst evSubst e =
              ESubst (apply s exprSubst) (apply s evSubst) (s # e)
              where apply s ps = [(v, s # x) | (v, x) <- ps]
          s # EMatch m       = EMatch (s # m)
          s # EApp e e'      = EApp (s # e) (s # e')
          s # EBitSelect e f = EBitSelect (s # e) f
          s # EBitUpdate e f e' = EBitUpdate (s # e) f (s # e')
          s # EStructInit c es = EStructInit c [(f, s # e) | (f, e) <- es]
          s # EBind ta tb tm me v e e' =
              EBind (s # ta) (s # tb) (s # tm) (s # me) v (s # e) (s # e')
          s # EReturn e      = EReturn (s # e)
          s # EMethod ev n ts evs =
              EMethod (s # ev) n (s # ts) (s # evs)

instance HasEvidenceVariables Expr
    where fevs (ELamVar {})                    = []
          fevs (ELetVar tapp)                  = fevs tapp
          fevs (EBits {})                      = []
          fevs (ECon tapp)                     = fevs tapp
          fevs EBitCon{}                       = []
          fevs (ELam _ _ body)                 = fevs body
          fevs (ELet ds body)                  = fevs ds ++ fevs body
          fevs (ELetTypes _ e)                 = fevs e
          fevs (ESubst exprSubst evSubst body)
              = fevs (map snd exprSubst) ++ fevs (map snd evSubst) ++ filter (`notElem` bound) (fevs body)
              where bound = map fst evSubst
          fevs (EMatch m)                      = fevs m
          fevs (EApp e e')                     = fevs e ++ fevs e'
          fevs (EBitSelect e f)                = fevs e
          fevs (EBitUpdate e f e')             = fevs e ++ fevs e'
          fevs (EStructInit _ es)              = concatMap (fevs . snd) es
          fevs (EBind ta tb tm me v e e')      = fevs me ++ fevs e ++ fevs e'
          fevs (EReturn e)                     = fevs e

instance HasTypeVariables Ev
    where s # e@(EvVar {})      = e
          s # EvCons tapp       = EvCons (s # tapp)
          s # EvRequired v es   = EvRequired v (s # es)
          s # EvCases cs        = EvCases (catMaybes [do cond' <- cond `under` s; return (cond', s # ev) | (cond, ev) <- cs])
          s # e@(EvComputed {}) = e
          s # EvFrom p e e'     = EvFrom (s # p) (s # e) (s # e')

instance HasEvidenceVariables Ev
    where fevs (EvVar v)                       = [v]
          fevs (EvRequired _ es)               = fevs es
          fevs (EvCons tapp)                   = fevs tapp
          fevs (EvCases cs)                    = concat [fevs ev | (_, ev) <- cs]
          fevs (EvComputed {})                 = []
          fevs (EvFrom EvWild e e')            = fevs e ++ fevs e'
          fevs (EvFrom (EvPat _ _ evars) e e') = fevs e ++ filter (`notElem` evars) (fevs e')


instance HasTypeVariables EvPat
    where s # EvPat id ts ps = EvPat id (s # ts) ps
          s # EvWild         = EvWild

filterSubst vs (S m) =
    S (Map.filterWithKey (\v _ -> v `notElem` vs) m)

instance HasTypeVariables t => HasTypeVariables (Gen t)
    where -- I'm not sure if the filter in this expression is necessary.  It's definitely correct,
          -- but the existing compiler pipeline should not result in code with shadowing type
          -- parameters.
          s # Gen typarams evparams body = Gen typarams evparams (filterSubst typarams s # body)

instance HasEvidenceVariables t => HasEvidenceVariables (Gen t)
    where fevs (Gen typarams evparams body) = filter (`notElem` evparams) (fevs body)

instance HasTypeVariables Inst
    where s # Inst id ts ev = Inst id (s # ts) (s # ev)

instance HasEvidenceVariables Inst
    where fevs (Inst id ts ev) = fevs ev

instance HasTypeVariables Match
    where _ # MFail        = MFail
          s # MCommit e    = MCommit (s # e)
          s # MElse m m'   = MElse (s # m) (s # m')
          s # MGuarded g m = MGuarded (s # g) (s # m)

instance HasEvidenceVariables Match
    where fevs MFail          = []
          fevs (MCommit e)    = fevs e
          fevs (MElse m m')   = fevs m ++ fevs m'
          fevs (MGuarded (GFrom (PCon inst vs) id) m)
                              = fevs inst ++ fevs m
          fevs (MGuarded g m) = fevs g ++ fevs m

instance HasTypeVariables Pattern
    where _ # PWild               = PWild
          s # PVar id tys         = PVar id (s # tys)
          s # PCon inst vs        = PCon (s # inst) vs

instance HasEvidenceVariables Pattern
    where fevs PWild          = []
          fevs (PVar {})      = []
          fevs (PCon {})      = []

instance HasTypeVariables Guard
    where s # GFrom p id              = GFrom (s # p) id
          s # GLet ds                 = GLet (s # ds)
          s # GSubst evs              = GSubst evs'
              where evs' = [(v, s # ev) | (v, ev) <- evs]
          s # GLetTypes (Left cs)     = GLetTypes (Left (catMaybes [do cond' <- cond `under` s; impr' <- impr `under` s; return (cond', impr') | (cond, impr) <- cs]))
          s # g@(GLetTypes (Right _)) = g

instance HasEvidenceVariables Guard
    where fevs (GFrom p id)   = fevs p
          fevs (GLet ds)      = fevs ds
          fevs (GSubst evs)   = concatMap (fevs . snd) evs
          fevs (GLetTypes cs) = []

instance HasTypeVariables Defn
    where s # Defn name tys (Right body) = Defn name (s # tys) (Right (s # body))
          s # Defn name tys (Left body) = Defn name (s # tys) (Left body)

instance HasEvidenceVariables Defn
    where fevs (Defn _ _ (Right body)) = fevs body
          fevs (Defn _ _ (Left _)) = []

instance HasTypeVariables Decls
    where s # Decls ds = Decls (s # ds)

instance HasEvidenceVariables Decls
    where fevs (Decls gs) = concatMap fevs gs

instance HasTypeVariables (TopDecl KId)
  where s # d@(Datatype id params ctors)   = d
        s # d@(Bitdatatype id width ctors) = d
        s # d@(Struct id width fields)     = d
        s # d@(Area v ids t w o)           = Area v [(id, s # tapp) | (id, tapp) <- ids] (s # t) w o

----------------------------------------------------------------------------------------------------

class HasTypeVariables t => Unifies t
    where unify :: t -> t -> Maybe TSubst

varBind :: KId -> Type -> Maybe TSubst
varBind v (TyVar w)
    | v == w = Just empty
varBind v t
    | v `elem` tvs t     = Nothing
    | kind v /= kindOf t = Nothing
    | otherwise          = Just (singleton v t)

instance Unifies Type
    where unify (TyCon id) (TyCon id')
              | id == id' = Just empty
              | otherwise = Nothing
          unify t (TyVar v) = varBind v t
          unify (TyVar v) t = varBind v t
          unify (TyApp t t') (TyApp u u') =
              do s <- unify t u
                 s' <- unify (s # t') (s # u')
                 return (s' `compose` s)
          unify (TyNat n) (TyNat n')
              | n == n'   = Just empty
              | otherwise = Nothing
          unify (TyLabel l) (TyLabel l')
              | l == l'   = Just empty
              | otherwise = Nothing
          unify _ _ = Nothing

instance Unifies t => Unifies [t]
    where unify [] [] = Just empty
          unify (t:ts) (u:us) =
              do s <- unify t u
                 s' <- unify (s # ts) (s # us)
                 return (s' `compose` s)
          unify _ _ = Nothing
