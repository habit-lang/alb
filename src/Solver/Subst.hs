{-# LANGUAGE DeriveFunctor, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, TupleSections #-}
module Solver.Subst where

import Control.Monad.State
import qualified Data.IntSet as Set
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import qualified Syntax.IMPEG.KSubst as K
import Solver.PP
import Solver.Syntax
import Solver.Trace

----------------------------------------------------------------------------------------------------
-- Substitution types
--
-- Note: the actual substitution types are defined in Solver.Syntax, because the Subst type is used
-- in defining the Proof type.
--
-- As mentioned there, the trail contains a "tagged substitution", in which each binding is
-- associated with an index, used to identify steps depending on that binding.  When applying such a
-- substitution, we will need to collect a list of all the assumptions used.  On the other hand,
-- many substitutions are used without being added to the trail, and the introduction and collection
-- of assumption indices would be burdensome in those cases.
--
-- To abstract over both usage patterns, we introduce a class 'Substitution s m', where 's' is a
-- type of substitution (Subst or TaggedSubst) and 'm' is a monad capturing the additional
-- information generated when applying the substitution.

class Monad m => SubstitutionResult m
    where plain :: m t -> t

class SubstitutionResult m => Substitution s m | s -> m
    where empty          :: s
          compose        :: s -> s -> s
          isEmpty        :: s -> Bool
          domain         :: s -> [TyId]
          findBinding    :: TyId -> s -> Maybe (m Type)
          consistent     :: s -> s -> Bool

-- Untagged substitutions generate no additional information during substitution application, so we
-- use the identity monad.

newtype Identity t = Identity t deriving (Eq, Show, Functor)

instance Applicative Identity
    where pure = return
          (<*>) = liftM2 ($)

instance Monad Identity
    where return           = Identity
          Identity x >>= f = f x

instance SubstitutionResult Identity
    where plain (Identity x) = x

instance Substitution Subst Identity
    where empty                         = S K.empty []
          compose (S ks ps) (S ks' ps') = S (K.compose ks' ks) (ps' ++ ps)
          isEmpty (S ks ps)             = K.isEmpty ks && null ps
          domain (S _ ps)               = [v | (v :-> _) <- ps]

          findBinding v s@(S ks mappings) =
              do (bs, t) <- iter [] mappings
                 return (S ks bs # t)
              where iter bs [] = Nothing
                    iter bs (b@(v' :-> t) : rest)
                        | v == v' = Just (reverse bs, t)
                        | otherwise = iter (b:bs) rest

          consistent s@(S ks _) s'@(S ks' _) = K.consistent ks ks' && all consistentAt vs
              where vs = domain s `intersect` domain s'
                    consistentAt v = findBinding v s == findBinding v s'

-- Tagged substitutions generate a set of indices during application.  The type 'WithInts t'
-- combines a value of type 't' with a set of integers.  This amounts to the standard Writer
-- monad for lists of integers, but without the generalization over arbitrary Monoids used in
-- the definition of Writer and WriterT.

data WithInts x = W x Set.IntSet

instance Functor WithInts
    where fmap f (W x is) = W (f x) is

instance Applicative WithInts
    where pure = return
          (<*>) = liftM2 ($)

instance Monad WithInts
    where return x     = W x Set.empty
          W x is >>= f = let W y is' = f x
                         in W y (Set.union is is')

instance SubstitutionResult WithInts
    where plain (W x _) = x

instance Substitution TaggedSubst WithInts
    where empty                           = TS K.empty []
          compose (TS ks ps) (TS ks' ps') = TS (K.compose ks' ks) (ps' ++ ps)
          isEmpty (TS ks ps)              = K.isEmpty ks && null ps
          domain (TS _ ps)                = [v | (_, v :-> _) <- ps]

          findBinding v s@(TS ks mappings) =
              do (bs, t, i) <- iter [] mappings
                 let W t' is = TS ks bs # t
                 return (W t' (Set.insert i is))
              where iter bs [] = Nothing
                    iter bs (b@(i, v' :-> t) : rest)
                        | v == v' = Just (reverse bs, t, i)
                        | otherwise = iter (b:bs) rest

          consistent s@(TS ks _) s'@(TS ks' _) = K.consistent ks ks' && all consistentAt vs
              where vs = domain s `intersect` domain s'
                    consistentAt v = fmap plain (findBinding v s) == fmap plain (findBinding v s')

assumptionIds          :: TaggedSubst -> [Int]
assumptionIds (TS _ ps) = map fst ps

-- Compose a list of substitutions, as long as they're consistent.  Returns Nothing if they were
-- inconsistent.
concatSubsts :: [Subst] -> Maybe Subst -- Substitution s t => [s] -> Maybe s
concatSubsts [] = Just empty
concatSubsts (s:ts) =
    do t <- concatSubsts ts
       case s `under` t of
         Left _ -> Nothing
         Right s' -> Just (s' `compose` t)

-- Under attempts to factor a substitution:
-- [Maybe Int/t] `under` [Maybe u/t]  ===>  [Int/u]
-- s1 `under` s2 = s where s `compose` s2 == s1 (except that the lhs may have a larger domain).
under :: Substitution s m => Subst -> s -> UnificationResult
under (S ks []) s' = return (S ks [])
under (S ks ((v :-> t) : rest)) s' =
    case plain `fmap` findBinding v s' of
      Nothing ->
          do (S ks' bs') <- varBind False [] v (s' ## t)
             (S ks'' bs'') <- under (S ks rest) s'
             return (S (K.compose ks' ks'') (bs' ++ bs''))
      Just t' ->
          do (S ks' bs') <- unify ([], []) (s' ## t) t'
             (S ks' bs'') <- under (S (K.compose ks ks') rest) s'
             return (S ks' (bs' ++ bs''))

-- Assumption in partitionSubst is that the list of TyIds contains new variables, so there will
-- not be any references to those type vars in other parts of the substitution.  (e.g., use this
-- after instantiating a scheme with fresh type vars and then matching.)

partitionSubst :: [TyId] -> Subst -> (Subst, Subst)
partitionSubst vs (S ks bs) = (S ks bsIn, S ks bsOut)
    where (bsIn, bsOut) = partition (\(v :-> _) -> v `elem` vs) bs

-----------------------------------------------------------------------------------------------------
-- Substitution: we define a class "HasVars" for things that have variables, and define substitution
-- application (#) as a method of the class.  There are instances for the usual suspects.

infixr 6 #, ##
class HasVars t
    where vars :: t -> [TyId]
          ovars, tvars :: Opacities -> t -> [TyId]   -- o=opaque, t=transparent
            -- e.g., ovars opacities t = all the vars that only appear in opaque positions in t
          (#) :: Substitution s m => s -> t -> m t

          inst :: [Type] -> t -> t
          gen  :: Int -> [TyId] -> t -> t

(##)  :: (Substitution s m, HasVars t) => s -> t -> t
s ## x = plain (s # x)

instance HasVars t => HasVars [t]
    where vars = nub . concatMap vars
          tvars ops = nub . concatMap (tvars ops)
          ovars ops xs = nub (concatMap (ovars ops) xs \\ concatMap (tvars ops) xs)
          s # xs = mapM (s #) xs

          inst ts = map (inst ts)
          gen n is = map (gen n is)

instance HasVars Type
    where vars (TyCon {}) = []
          vars (TyVar s) = [s]
          vars (TyLit {}) = []
          vars (TyGen _)  = []
          vars (t1 :@ t2) = nub (vars t1 ++ vars t2)

          tvars _ t = vars t
          ovars _ t = []

          s # t@(TyCon {}) = return t
          s # TyVar v =
              case findBinding v s of
                Nothing -> return (TyVar v)
                Just mt -> mt
          s # t@(TyLit {}) = return t
          s # t@(TyGen _)  = return t
          s # (t1 :@ t2) = liftM2 (:@) (s # t1) (s # t2)

          inst ts (TyGen n) = ts !! n
          inst ts (t :@ t') = inst ts t :@ inst ts t'
          inst _ t          = t

          gen n is (TyVar v) = case elemIndex v is of
                                 Just n' -> TyGen (n + n')
                                 Nothing -> TyVar v
          gen n is (t :@ t') = gen n is t :@ gen n is t'
          gen _ _ t          = t

filterIdxs :: [Int] -> [t] -> [t]
filterIdxs is xs = loop 0 xs
    where loop _ []                   = []
          loop n (x:xs) | n `elem` is = x : loop (n + 1) xs
                        | otherwise   = loop (n + 1) xs

partitionIdxs :: [Int] -> [t] -> ([t], [t])
partitionIdxs is xs = loop 0 xs
    where loop _ []                   = ([], [])
          loop n (x:xs) | n `elem` is = (x:ys, zs)
                        | otherwise   = (ys, x:zs)
              where (ys, zs) = loop (n + 1) xs

instance HasVars Pred
    where vars (Pred _ ts _ _) = vars ts

          tvars ops (Pred c ts _ _) = nub (concatMap (tvars ops) (filterIdxs transparentPositions ts))
              where opaquePositions      = fromMaybe [] (lookup c ops)
                    transparentPositions = filter (`notElem` opaquePositions) [0..length ts]
          ovars ops (Pred c ts _ _) = nub (concatMap vars opaqueArgs \\ concatMap vars transparentArgs)
              where opaquePositions = fromMaybe [] (lookup c ops)
                    (opaqueArgs, transparentArgs) = partitionIdxs opaquePositions ts

          s # Pred n ts x loc = do ts' <- s # ts
                                   return (Pred n ts' x loc)

          inst ts (Pred cl ts' f loc) = Pred cl (inst ts ts') f loc
          gen n is (Pred cl ts f loc) = Pred cl (gen n is ts) f loc

instance HasVars t => HasVars (Qual t)
    where vars (qs :=> p) = nub (vars qs ++ vars p)

          tvars ops (qs :=> p) = nub (tvars ops qs ++ tvars ops p)
          ovars ops (qs :=> p) = nub ((ovars ops qs ++ ovars ops p) \\ (tvars ops qs ++ tvars ops p))

          s # qs :=> p = liftM2 (:=>) (s # qs) (s # p)

          inst ts (qs :=> p) = inst ts qs :=> inst ts p
          gen n is (qs :=> p) = gen n is qs :=> gen n is p

instance HasVars t => HasVars (u, t)
    where vars (_, x) = vars x

          tvars ops (_, x) = tvars ops x
          ovars ops (_, x) = ovars ops x

          s # (v, x) = liftM (v,) (s # x)

          inst ts (v, x) = (v, inst ts x)
          gen n is (v, x) = (v, gen n is x)

instance HasVars Requirement
    where vars (Requires p ps) = nub (vars p ++ vars ps)

          tvars ops (Requires p ps) = nub (tvars ops p ++ tvars ops ps)
          ovars ops (Requires p ps) = nub ((ovars ops p ++ ovars ops ps) \\ (tvars ops p ++ tvars ops ps))

          s # Requires p ps = liftM2 Requires (s # p) (s # ps)

          inst ts (Requires p ps) = Requires (inst ts p) (inst ts ps)
          gen n is (Requires p ps) = Requires (gen n is p) (gen n is ps)

instance HasVars ProofPattern
    where s # Pat axid ts vs =
              do ts' <- s # ts
                 return (Pat axid ts' vs)
          s # Wild           = return Wild

          vars  = error "vars ProofPattern"
          ovars = error "ovars ProofPattern"
          tvars = error "tvars ProofPattern"
          inst  = error "inst ProofPattern"
          gen   = error "gen ProofPattern"

----------------------------------------------------------------------------------------------------
-- Unification and matching

type UnificationResult = Either String Subst

-- The definition of 'fail' in the Monad instance for Either causes a run-time error instead of
-- using Left.  This makes sense.
failWith :: String -> Either String Subst
failWith = Left

singleton' :: K.KSubst -> TyId -> Type -> UnificationResult
singleton' ks v t = Right (S ks [v :-> t])

singleton :: TyId -> Type -> UnificationResult
singleton  = singleton' K.empty

class HasVars t => Unifies t
    where unifyGeneral :: Bool -> ([TyId], [Id]) -> t -> t -> UnificationResult
          -- first parameter identifies generics (generic type vars, generic kind vars);
          -- unification is not allowed to bind these variables.

          -- (pred `match` rule) is true iff there is a subst for rule to make it
          -- match pred - it doesn't substitute into pred
          matchGeneral :: Bool -> ([TyId], [Id]) -> t -> t -> UnificationResult

unify, unifyInfinitary, match, matchInfinitary :: Unifies t => ([TyId], [Id]) -> t -> t -> UnificationResult
unify = unifyGeneral False
unifyInfinitary = unifyGeneral True
match = matchGeneral False
matchInfinitary = matchGeneral True

instance Unifies t => Unifies [t]
    where unifyGeneral _ _ [] [] = return empty
          unifyGeneral infinitary gvars (t:ts) (u:us) =
              do s <- unifyGeneral infinitary gvars t u
                 s' <- unifyGeneral infinitary gvars (s ## ts) (s ## us)
                 return (s `compose` s')
          unifyGeneral _ _ _ [] = failWith "Subst:48"
          unifyGeneral _ _ [] _ = failWith "Subst:49"

          matchGeneral _ _ [] [] = return empty
          matchGeneral infinitary gvars (t:ts) (u:us) =
              do s <- matchGeneral infinitary gvars t u
                 s' <- matchGeneral infinitary gvars ts us
                 if consistent s s'
                   then return (s `compose` s')
                   else failWith "MatchGeneral inconsistent"
          matchGeneral _ _ _ [] = failWith "Subst:70"
          matchGeneral _ _ [] _ = failWith "Subst:71"

cannotUnifyGeneral a b            = failWith ("Cannot unify \"" ++ ppx a ++ "\" with \"" ++ ppx b ++ "\"")
cannotMatchGeneral a b            = failWith ("Cannot match \"" ++ ppx a ++ "\" against \"" ++ ppx b ++ "\" (note that match cannot substitute for variables on the lhs)")
occursCheck (Kinded v _) t = failWith ("Cannot construct the infinite type " ++ ppx v ++ " = " ++ ppx t)
kindsDontMatchGeneral k k'        = failWith ("Cannot unify type of kind " ++ ppx k ++ " with type of kind " ++ ppx k')
matchInconsistent          = failWith "Match inconsistent"

varBind :: Bool -> [Id] -> TyId -> Type -> UnificationResult
varBind infinitary gkvars (Kinded name k) (TyVar (Kinded name' k'))
    | name == name' =
        case K.unify gkvars k k' of
          Left _   -> kindsDontMatchGeneral k k'
          Right ks -> return (S ks [])
varBind infinitary gkvars v@(Kinded name k) t
    | not infinitary && v `elem` vars t = occursCheck v t
    | otherwise       =
        case K.unify gkvars k k' of
          Left _   -> kindsDontMatchGeneral k k'
          Right ks -> singleton' ks v t
    where k' = kindOf t

instance Unifies Type
    where unifyGeneral _ _ (TyCon s) (TyCon s')
              | s == s' = return empty
          unifyGeneral infinitary gvars (t :@ u) (t' :@ u') =
              do s <- unifyGeneral infinitary gvars t t'
                 s' <- unifyGeneral infinitary gvars (s ## u) (s ## u')
                 return (s `compose` s')
          unifyGeneral _ _ (TyVar v) (TyVar w)
              | v == w = return empty
          unifyGeneral infinitary (gtvs, gkvs) t (TyVar v)
              | v `notElem` gtvs = varBind infinitary gkvs v t
          unifyGeneral infinitary (gtvs, gkvs) (TyVar v) t
              | v `notElem` gtvs = varBind infinitary gkvs v t
          unifyGeneral _ _ (TyLit i) (TyLit j)
              | i == j           = return empty
          unifyGeneral _ _ t u = cannotUnifyGeneral t u

          matchGeneral _ _ (TyCon s) (TyCon s')
              | s == s' = return empty
          matchGeneral infinitary gvars (t :@ u) (t' :@ u') =
              do s <- matchGeneral infinitary gvars t t'
                 s' <- matchGeneral infinitary gvars u u'
                 if consistent s s'
                 then return (s `compose` s')
                 else matchInconsistent
          matchGeneral _ _ (TyVar v) (TyVar w)
              | v == w = return empty
          matchGeneral infinitary (gtvs, gkvs) t (TyVar v)
              | v `notElem` gtvs = varBind infinitary gkvs v t
          matchGeneral _ _ (TyLit i) (TyLit j)
              | i == j           = return empty
          matchGeneral _ _ t u = cannotMatchGeneral t u

instance Unifies Pred
    where unifyGeneral infinitary gvars (Pred n ts x _) (Pred n' ts' x' _)
              | n /= n'   = cannotUnifyGeneral n n'
              | x /= x'   = cannotUnifyGeneral x x'
              | otherwise = unifyGeneral infinitary gvars ts ts'

          matchGeneral infinitary gvars (Pred n ts x _) (Pred n' ts' x' _)
              | n /= n'   = cannotMatchGeneral n n'
              | x /= x'   = cannotMatchGeneral x x'
              | otherwise = matchGeneral infinitary gvars ts ts'

instance Unifies t => Unifies (Qual t)
    where unifyGeneral infinitary gvars (qs :=> p) (qs' :=> p') =
              do s <- unifyGeneral infinitary gvars qs qs'
                 s' <- unifyGeneral infinitary gvars (s ## p) (s ## p')
                 return (s `compose` s')
          matchGeneral infinitary gvars (qs :=> p) (qs' :=> p') =
              do s <- matchGeneral infinitary gvars qs qs'
                 s' <- matchGeneral infinitary gvars p p'
                 if consistent s s'
                 then return (s `compose` s')
                 else matchInconsistent
