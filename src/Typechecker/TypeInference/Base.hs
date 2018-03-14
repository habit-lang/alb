{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances, ScopedTypeVariables#-}
module Typechecker.TypeInference.Base where

import Prelude hiding ((<$>))

import Common
import Control.Monad
import Control.Monad.State
import Data.List (intercalate, nub, partition, (\\))
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Printer.Common hiding (empty)
import Printer.IMPEG hiding (bindingTyVar, tyvarName)
import qualified Solver as Solver
import Syntax.Common
import Syntax.IMPEG
import qualified Syntax.IMPEG.KSubst as K
import Syntax.IMPEG.TSubst
import qualified Syntax.XMPEG as X
import qualified Syntax.XMPEG.TSubst as X
import qualified Utils.BDD as BDD

import Data.IORef
import qualified Debug.Trace as Trace
import System.IO.Unsafe

{-# NOINLINE trace #-}
{-# NOINLINE doTrace #-}

substStr s = unlines ["    " ++ fromId v ++ " +-> " ++ show (ppr t) | let S m = s, (Kinded v _, t) <- Map.assocs m]
traceSubst msg (ks, s) = trace (msg ++ "\n" ++ substStr s)
traceIf b s x = if b then trace s x else x
doTrace = unsafePerformIO (newIORef False)
trace s x = unsafePerformIO (do b <- readIORef doTrace
                                when b (Trace.traceIO s)
                                return x)

----------------------------------------------------------------------------------------------------
-- Types and type synonyms

type Ty          = Type KId
type QTy         = Qual (PredType Pred KId) Ty
type TyS         = Scheme Pred KId

data Binding     = LetBound (KScheme TyS)
                 | LamBound Ty

instance Show Binding where
  show (LetBound (ForallK tys _)) = "LetBound (" ++ (show tys) ++ ")"
  show (LamBound a) = "LamBound" ++ (show a)

letBoundType    :: Ty -> Binding
letBoundType t   = LetBound (ForallK [] (Forall [] ([] :=> introduced t)))

instance K.HasKinds Binding
    where vars (LetBound ksc) = K.vars ksc
          vars (LamBound ty)  = K.vars ty

          s # (LetBound ksc) = LetBound (s K.# ksc)
          s # (LamBound ty)  = LamBound (s K.# ty)

instance HasTypeVariables Binding KId
    where tvs (LetBound (ForallK _ tys)) = tvs tys
          tvs (LamBound ty)              = tvs ty

          s # LetBound (ForallK vs tys)  = LetBound (ForallK vs (s # tys))
          s # LamBound ty                = LamBound (s # ty)

          inst _ _                       = error "inst applied to Binding"
          gen _ _ _                      = error "gen applied to Binding"

instance HasTypeVariables (Binding, [[Id]]) KId
    where tvs ((LetBound (ForallK _ tys)), is) = tvs tys
          tvs ((LamBound ty), is)              = tvs ty

          s # (LetBound (ForallK vs tys), is)  = (LetBound (ForallK vs (s # tys)), is)
          s # (LamBound ty, is)                = (LamBound (s # ty), is)

          inst _ _                       = error "inst applied to Binding"
          gen _ _ _                      = error "gen applied to Binding"


-- For linear types we have 2 kinds of environment entities
-- a. [a:x, b:y]
-- b. [a:x, (b:y;c:z)]

-- To adhere to the same Map kind of structure,
-- our Map will look like Id -> (Binding, [other Ids it has ; relationship with current Id])
-- a. will look like [(a -> (x,[])), (b -> (y, []))]
-- b. will look like [(a -> (x, [])), (b -> (y, [b, c]), (c -> (z, [b, c]))]

-- scope is to identify whether the id is defined locally or globally
data Scope = Local | Global
  deriving (Eq, Show, Ord)
type TyEnv       = Map Id (Binding, [[Id]], Scope)
type CtorEnv     = Map Id ((KScheme TyS, Int), [[Id]], Scope)

-- restricts the type environment to local scope
local :: TyEnv -> TyEnv
local = Map.filter (\(_, _, scope) -> scope == Local)

-- returns all the variables that have sharing with current variable
closure :: TyEnv -> Id -> [Id]
closure tyenv i = nub $ concat $ filter (i `elem`) lstOflst
  where (lstOflst::[[Id]]) = concat $ map (\(_, shids, _) -> shids) $ Map.elems tyenv

closureHelper :: TyEnv -> [Id] -> Set Id
closureHelper tyenv is = Set.unions $ map (\l -> Set.fromList l) (map (closure tyenv) is)

tyEnvFromCtorEnv :: CtorEnv -> TyEnv
tyEnvFromCtorEnv = Map.map (\(bnds, shids, scope) -> ((LetBound $ fst bnds), shids, scope))

instance HasTypeVariables TyEnv KId
    where tvs _  = []
          s # env = applyToEnvironment (K.empty, s) env

          inst _ _ = error "inst applied to TyEnv"
          gen _ _ _ = error "gen applied to TyEnv"

applyToEnvironment :: Unifier -> TyEnv -> TyEnv
applyToEnvironment u@(ks, s) m = if isEmpty s && K.isEmpty ks then m else Map.map f m
  where
    f :: (Binding, [[Id]], Scope) -> (Binding, [[Id]], Scope)
    f (t, shids, scope) = {-# SCC "u##" #-} (u ## t, shids, scope)

showTypeEnvironment :: TyEnv -> String
showTypeEnvironment valenv = unlines [fromId v ++ " :: " ++ showBinding b | (v, b) <- Map.assocs valenv]
    where showBinding (LetBound tys, shids, scope) = show (ppr tys) ++ (show shids) ++ (show scope)
          showBinding (LamBound ty, shids, scope)  = show (ppr ty) ++ (show shids) ++ (show scope)

data ClassEnv      = ClassEnv { solverEnvironment      :: Solver.SolverEnv
                              , functionalDependencies :: Map Id [Fundep Int]
                              , methodSignatures       :: Map Id ([KId], [(Id, KScheme TyS)])
                              , defaultMethods         :: Map (Id,Id) Id }   -- (class, member) |-> impl name

type Preds         = [(Id, Located (Pred (Located Ty)))] -- Predicates to be solved, paired with evidence variables
type EvSubst       = [(Id, X.Ev)]              -- Predicates solved, paired with evidence variables
type ConditionalBindings = Either [([(KId, X.Type)], [(KId, X.Type)])] ([KId], [KId], [X.Type] -> [X.Type])
type RequirementT = ([Located (PredType Pred KId)], [Located (PredType Pred KId)])

type BitdataCtorEnv  = Map Id (Ty, [(Id, Ty, Maybe Id)])
type StructRegionEnv = Map Id (Ty, [(Maybe Id, Ty, Maybe Id)])  -- struct name -> (type, [(field name, type, def init)])
type BitdataBDDEnv   = Map Id BDD.Pat

-- Invariants: the current substitution is already applied to the type environment
data TcState     = TcState { typeEnvironment     :: TyEnv
                           , ctorEnvironment     :: CtorEnv
                           , classEnvironment    :: ClassEnv
                           , genericVars         :: ([KId], [Id])
                           , currentSubstitution :: Unifier
                           , bitdataCtors        :: BitdataCtorEnv
                           , bitdataBDDs         :: BitdataBDDEnv
                           , structRegions       :: StructRegionEnv
                           , requirementTemplates :: [RequirementT] }

type Exp         = Expr Pred KId

-- In addition to a t, a TcRes t includes:
--   - New assumed predicates
--   - New required predicates
--   - Used names
-- At various points (currently all linearity-related) we have mini-simplification problems.  Rather
-- than invoke the solver for each of these, we return both the assumed and requried predicates from
-- each, and call the solver only at generalization.
--
-- TODO: perhaps this suggests incorporating assumed, goals, and used as writer-y bits of the
-- TcState rather than explicitly in each return type?

data TcResult t = R { payload :: t
                    , assumed :: Preds
                    , goals :: Preds
                    , used :: [Id] } -- can use we use this for using linear predicates
type TcRes t = M (TcResult t)

----------------------------------------------------------------------------------------------------
-- Solver interface

-- TODO: rename 'solve' to 'simplify'?  Seems to me to more accurate characterize what it does.
-- Problem: how to similarly rename 'entails'.

solve :: [KId] -> [KId] -> Preds -> M (EvSubst, Preds, [ConditionalBindings])
solve tvs0 outputVariables ps = entails tvs0 outputVariables [] ps

entails :: [KId] -> [KId] -> Preds -> Preds -> M (EvSubst, Preds, [ConditionalBindings])
entails transparents outputVariables hypotheses conclusions =
    do (s, evs, ps, cbinds) <- entails' transparents outputVariables hypotheses conclusions
       when (not (isEmptyU s)) $
           traceSubst "Computed improvement" s $
               modify (\st -> st { currentSubstitution = s `composeU` currentSubstitution st })
       return (evs, ps, cbinds)

entails' :: [KId] -> [KId] -> Preds -> Preds -> M (Unifier, EvSubst, Preds, [ConditionalBindings])
entails' transparents outputVariables hypotheses conclusions =
    do subst    <- gets currentSubstitution
       classEnv <- gets classEnvironment
       gvars    <- gets genericVars
       z        <- M (lift getCounter)
       let -- How do we get unsubstituted type variables?
           substitute ps    = [(id, subst ## p) | (id, p) <- ps]
           hypotheses'      = substitute hypotheses
           conclusions'     = substitute conclusions
           transparents'    = tvs [subst ## TyVar kid | kid <- transparents]
           outputVariables' = tvs [subst ## TyVar kid | kid <- outputVariables]
       case Solver.entails (solverEnvironment classEnv) gvars transparents' outputVariables' hypotheses' conclusions' z of  -- FIXME
         Left (At loc p) -> failWith (shorten p (hang 10 (group (text "Disproved" <+> ppr p <$> "arising at" <+> ppr loc))))
         Right (ev, ps, ks, impr, cbinds, z') ->
             do M (lift (putCounter z'))
                return ((ks, foldl (\s (id, ty) -> extend id (s # ty) s) empty impr),
                        ev, ps, cbinds)

----------------------------------------------------------------------------------------------------
-- Usual typechecking monad and monadic operations

-- Typechecker monad: failure is captured by a pair of error string and possible source location;
-- state is the current substitution and an integer for fresh name generation; environment includes
-- the value and class environments.

newtype M t = M { runM :: StateT TcState Base t }
    deriving (Functor, Applicative, Monad, MonadBase, MonadState TcState)

newTyVar :: Kind -> M Ty
newTyVar k = do v <- fresh "t"
                return (TyVar (Kinded v k))

instantiate :: MonadBase m => KScheme TyS -> m ([Id], [KId], QTy)
instantiate (ForallK ids (Forall kids qt)) =
    do knames <- mapM fresh ids
       names <- mapM fresh genNames
       let ksubst = K.new (zip ids (map KVar knames))
           kids'  = zipWith Kinded names ks
           ts     = map TyVar kids'
       return (knames, kids', ksubst K.# inst ts qt)
    where (genNames, ks) = unzip [(v, k) | Kinded v k <- kids]

-- Operations on the current substitution:
-- TODO: Unnecessary substitutions?

withGeneric :: MonadState TcState m => ([KId], [Id]) -> m t -> m t
withGeneric (gtvs, gkvs) c =
    traceIf (not (null gtvs)) (show ("Adding generics:" <+> cat (punctuate ", " (map ppr gtvs)))) $
    do modify (\st -> st { genericVars = (gtvs ++ fst (genericVars st), gkvs ++ snd (genericVars st)) })
       v <- c
       modify (\st -> st { genericVars = (drop (length gtvs) (fst (genericVars st)), drop (length gkvs) (snd (genericVars st))) })
       return v

instance Printable UnificationFailure
    where ppr (TypesFail Match t u) = "Unable to match " <+> ppr t <+> " against " <+> ppr u
          ppr (TypesFail Unify t u) = "Unable to unify " <+> ppr t <+> " with " <+> ppr u
          ppr (PredsFail Match p q) = "Unable to match " <+> ppr p <+> " against " <+> ppr q
          ppr (PredsFail Unify p q) = "Unable to unify " <+> ppr p <+> " with " <+> ppr q
          ppr (OccursCheck v t)     = "Unable to construct infinite type" <+> tyvarName v <+> equals <+> ppr t
          ppr (KindsDontMatch k k') = "Unable to unify variables of kinds" <+> ppr k <+> "and" <+> ppr k'
          ppr TypeNotGeneral        = "Type was less general than expected"
          ppr StructuralFail        = "Unexpected unification failure"

expect :: (Unifies t, Printable t) => (([KId], [Id]) -> t -> t -> Either UnificationFailure Unifier) -> t -> t -> M Unifier
expect f expected actual =
    do gvars     <- gets genericVars
       expected' <- substitute expected
       actual'   <- substitute actual
       case f gvars expected' actual' of
         Left err -> failWith (shorten expected' $ shorten actual' $
                               align (text "Type error: " <+> ppr err <$>
                                      text "Expected:  " <+> ppr expected'  <$>
                                      text "Found:     " <+> ppr actual'))
         Right u  -> do modify (\st -> st { currentSubstitution = u `composeU` currentSubstitution st })
                        traceIf (not (isEmpty (snd u)))
                                (show (group (nest 4 ("Unification:" <$> "Expected: " <+> ppr expected' <> semi <$>
                                                      "Found" <+> ppr actual' <> semi <$>
                                                      "Generic:" <+> hsep (punctuate "," (map ppr (fst gvars))))) <$>
                                       text (substStr (snd u))))
                                (return u)

unifies, matches :: (Unifies t, Printable t) => t -> t -> M Unifier
unifies = expect unify
matches = expect match

substitute :: (K.HasKinds t, HasTypeVariables t KId, MonadState TcState m) => t -> m t
substitute t = do s <- gets currentSubstitution
                  return (s ## t)

-- Operations on the class environment:

assert :: (Solver.SolverEnv -> Either String (t, Solver.SolverEnv)) -> M t
assert c =
    do st <- get
       let cenv = classEnvironment st
       case c (solverEnvironment cenv) of
         Left err -> failWithS err
         Right (v, senv') -> do put st { classEnvironment = cenv { solverEnvironment = senv' } }
                                return v

-- Linearity

-- TODO: the manipulation of locations is entirely suspect; many (if not all) of the linearity
-- predicates end up with "introduced" locations, which are of no benefit to the programmer at all.
-- [ANI] Is this is because we never pass the location information for prediates in checkProgram?
--       Predicates do not store any intrinsic information about their own location

buildLinPred :: Location -> (Located Ty -> Pred (Located Ty)) -> Binding -> M (Preds, (Id, Located (Pred (Located Ty))))
buildLinPred loc f (LetBound tys) =
    do (_, tyids, ps :=> t) <- instantiate tys
       let ps' = map (At loc . unrestricted . At loc . TyVar) tyids ++ ps
           p   = At loc (f t)
       evs <- freshFor "e" (p : ps')
       return (zip (tail evs) ps', (head evs, p))
buildLinPred loc f (LamBound t) =
    do ev <- fresh "e"
       return ([], (ev, At loc (f (At loc t))))

weaken :: Location -> [Id] -> [Id] -> M (Preds, Preds)
weaken loc introduced used =
    traceIf (not (null dropped)) (show ("Weakened:" <+> pprList' dropped)) $
    do (assumpss, goals) <- unzip `fmap` mapM weakenVar dropped
       return (concat assumpss, goals)
    where dropped = filter (`notElem` used) introduced
          weakenVar tyid = buildLinPred loc unrestricted =<< bindingOf tyid

weakenBranching :: Location -> [Id] -> [Id] -> M (Preds, Preds, [Id])
weakenBranching loc left right =
    do (assumpss, goals) <- unzip `fmap` mapM weakenVar justOne
       return (concat assumpss, goals, nub (left ++ right))
    where justOne = filter (`notElem` left) right ++ filter (`notElem` right) left
          weakenVar tyid = buildLinPred loc unrestricted =<< bindingOf tyid

-- We need to handle recursion differently from other bindings.  We introduce the recursive binding
-- regardless of whether or not it's needed.  However, if it was unneeded, we want to simply ignore
-- it, rather than introducing an unrestricted constraints.  (This corresponds to 'knowing' not to
-- wrap function definitions in a call to 'fix'.)  On the other hand, if it was used (even once),
-- then we do insist on introducing an unrestrictedness constraint.  This arises from the following
-- observation.
--
--  - First, the fixed point for unrestricted functions ((t -!> u) -!> (t -!> u)) -> (t -!> u) is
--    obviously unproblematic.
--
--  - Second, the fixed point for linear functions ((t -*> u) -!> (t -*> u)) -> (t -*> u) is
--    unproblematic only if the closure doesn't capture any linear values.  But in that case, it's
--    exactly equivalent to being unrestricted.
contractRecursive :: Location -> Id -> TcRes t -> TcRes t
contractRecursive loc id c =
    do r <- c
       if id `elem` used r
       then do (assumpsC, goalC) <- buildLinPred loc unrestricted =<< bindingOf id
               return r{ assumed = assumpsC ++ assumed r
                       , goals = goalC : goals r
                       , used = filter (id /=) (used r) }
       else return r

contract :: Location -> [Id] -> [Id] -> M (Preds, Preds, [Id])
contract loc left right =
    traceIf (not (null both)) (show ("Contracted:" <+> pprList' both)) $
    do (assumpss, goals) <- unzip `fmap` mapM contractVar both
       return (concat assumpss, goals, nub (left ++ right))
    where both = filter (`elem` left) right
          contractVar tyid = buildLinPred loc unrestricted =<< bindingOf tyid

contractMany :: Location -> [[Id]] -> M (Preds, Preds, [Id])
contractMany loc = foldM contract' ([], [], [])
    where contract' (assumps, goals, left) right =
              do (assumps', goals', left') <- contract loc left right
                 return (assumps' ++ assumps, goals' ++ goals, left')

-- Operations on the value environment:

bindingOf :: Id -> M Binding
bindingOf id = do s <- gets currentSubstitution
                  mt <- gets (Map.lookup id . typeEnvironment)
                  case mt of
                    Nothing -> failWithS ("Unbound identifier: " ++ fromId id)
                    Just (bnds, shids, scope)  -> return (s ## bnds)

-- We encapsulate the checks for weakening in the general binding operations.  That is, when binding
-- a set of 'x's, if the 'x's are not used in the contained operation, then the corresponding types
-- need to support weakening.  This check is implemented in 'binds'.  However, there are cases in
-- which we need to introduce typing assumptions that don't correspond to binding constucts,
-- particularly when checking (potentially) mutually recursive declaration blocks.  In these cases,
-- while multiple uses of variables should still introduce contraction (handled elsewhere),
-- variables that are unused should not introduced weakening (as they will be visible outside of the
-- current construct).  This case is handled by 'declare'.

-- TODO: this manipulation of state is awkward.  Should we actually prefer a stack-based
-- representation of the variable environment?
binds :: Location -> TyEnv -> TcRes t -> TcRes t
binds loc bs c = do modify (\st -> st { typeEnvironment = Map.union (typeEnvironment st) bs })
                    r <- c
                    tyenv' <- gets typeEnvironment
                    let shids = Set.toList $ closureHelper tyenv' (used r)
                    trace("DEBUG BINDS: " ++ (show (Map.keys bs))
                         ++ "\n\tsharing closure: " ++ show shids
                         ++ "\n\tused r: " ++ show (used r)
                         ++ "\n\ttyenv: " ++ show (local tyenv'))(return ())
                    -- Generate goals depending on the sharing closure of the current variable.
                    -- instead of the ones that only appear in the body
                    (assumpsC, goalsC) <- weaken loc vs (shids)
                    modify (\st -> st { typeEnvironment = Map.withoutKeys (typeEnvironment st) ((Set.fromList vs) `Set.difference` (Set.fromList shids))})
                    -- modify (\st -> st { typeEnvironment = Map.withoutKeys (typeEnvironment st) (Set.fromList $ vs \\ shids)})
                    tyenv'' <- gets typeEnvironment
                    trace("\tmodified tyenv: " ++ show (local tyenv''))(return())
                    return r{ assumed = assumpsC ++ assumed r
                            , goals = goalsC ++ goals r
                            , used = Set.toList $ Set.fromList $ (filter (`notElem` vs) (used r)) ++ (filter (`notElem` vs) (shids)) }
                            -- , used = filter (`notElem` vs) (used r) }
    where vs = Map.keys bs

bind :: Location -> Id -> Binding -> TcRes t -> TcRes t
bind loc x t = binds loc (Map.singleton x (t, [[x]], Local))

declare :: TyEnv -> M t -> M t
declare bs c =
    do modify (\st -> st { typeEnvironment = Map.union (typeEnvironment st) bs })
       r <- c
       modify (\st -> st { typeEnvironment = Map.filterWithKey (\v _ -> v `notElem` vs) (typeEnvironment st) })
       return r
    where vs = Map.keys bs

-- Operations on the constructor environment

bindCtors :: MonadState TcState m => CtorEnv -> m ()
bindCtors ctors = modify (\s -> s { ctorEnvironment = Map.union (ctorEnvironment s) ctors })

ctorBinding :: (MonadState TcState m, MonadBase m) => Id -> m ((KScheme TyS, Int), [[Id]], Scope)
ctorBinding id = do mt <- gets (Map.lookup id . ctorEnvironment)
                    case mt of
                      Nothing -> failWithS ("Unbound constructor function name " ++ fromId id)
                      Just t  -> return t

----------------------------------------------------------------------------------------------------
-- Type constants

arrowLike :: [Char] -> Ty
arrowLike id = TyCon (Kinded (Ident id 0 (Just (Fixity RightAssoc 5))) (KFun KStar (KFun KStar KStar)))

arrTy, bitTy, arefTy, labTy, initTy, bitdataCaseTy :: Ty
arrTy           = arrowLike "->"
bitTy           = TyCon (Kinded "Bit" (KFun KNat KStar))
arefTy          = TyCon (Kinded "ARef" (KFun KNat (KFun KArea KStar)))
labTy           = TyCon (Kinded "Proxy" (KFun KLabel KStar))
initTy          = TyCon (Kinded "Init" (KFun KArea KStar))
bitdataCaseTy   = TyCon (Kinded "BitdataCase" (KFun KStar (KFun KLabel KStar)))
bitdataCase t f = bitdataCaseTy @@ TyCon (Kinded t KStar) @@ TyLabel f

(@@) :: Ty -> Ty -> Ty
t @@ t' = TyApp (introduced t) (introduced t')
infixl 9 @@

to :: Ty -> Ty -> Ty
t `to` t' = arrTy @@ t @@ t'
infixr 5 `to`

-- [ANI] TODO we need to get this
allTo :: [Ty] -> Ty -> Ty
allTo = flip (foldr to)

-- Quill type constants

-- TODO: I don't know how many of these will actually turn out to be useful.
-- TODO: Above constants for arrow should not be used in Quill typechecking.

linArrTy, unrArrTy :: Ty
linArrTy = arrowLike "-*>"
unrArrTy = arrowLike "-!>"

newArrowVar :: M ((Id, Located (Pred (Located Ty))), Ty)
newArrowVar = do fv <- fresh "f"
                 let f = TyVar (Kinded fv (KFun KStar (KFun KStar KStar)))
                 e <- fresh "e"
                 return ((e, introduced (fun (introduced f))), f)

newStarArrowVar :: M ((Id, Located (Pred (Located Ty))), Ty)
newStarArrowVar = do fv <- fresh "f"
                     let f = TyVar (Kinded fv (KFun KStar (KFun KStar KStar)))
                     e <- fresh "e"
                     return ((e, introduced (sepFun (introduced f))), f)

newAmpArrowVar :: M ((Id, Located (Pred (Located Ty))), Ty)
newAmpArrowVar = do fv <-fresh "f"
                    let f = TyVar (Kinded fv (KFun KStar (KFun KStar KStar)))
                    e <- fresh "e"
                    return ((e, introduced (shFun (introduced f))), f)

linTo, unrTo :: Ty -> Ty -> Ty
t `linTo` u = linArrTy @@ t @@ u
t `unrTo` u = unrArrTy @@ t @@ u

starTo, ampTo :: Ty -> Ty -> M ((Id, Located (Pred (Located Ty))), Ty)
t `starTo` u = do (p, f) <- newStarArrowVar
                  return (p, f @@ t @@ u)

t `ampTo` u = do (p, f) <- newAmpArrowVar
                 return (p, f @@ t @@ u)

polyTo :: Ty -> Ty -> M ((Id, Located (Pred (Located Ty))), Ty)
t `polyTo` u = do (p, f) <- newArrowVar
                  return (p, f @@ t @@ u)

-- allUnrTo :: [Ty] -> Ty -> Ty
-- allUnrTo = flip (foldr unrTo)

-- allPolyTo :: [Ty] -> Ty -> M (Preds, Ty)
-- allPolyTo ts t = do (ps, fs) <- unzip `fmap` replicateM (length ts) newArrowVar
--                     return (ps, foldr (\(f, t) u -> f @@ t @@ u) t (zip fs ts))

-- Convenience functions for building predicates:

sumP :: Located Ty -> Located Ty -> Located Ty -> Pred (Located Ty)
sumP a b c = Pred "+" [a,b,c] Holds

predh n ts                           = Pred n ts Holds
predf n ts                           = Pred n ts Fails
byteSize a n                         = predh "ByteSize" [a, n]
bitSize t n                          = predh "BitSize" [t, n]
areaOf r a                           = predh "AreaOf" [r, a]
alignOf r n                          = predh "AlignOf" [r, n]
widthPred n                          = predh "Width" [n]
gcdPred n m p                        = predh "GCD" (map introduced [n, m, p])
lte m n                              = predh "<=" [m, n]
initablePred a                       = predh "Initable" [a]
procPred p                           = predh "Proc" [p]
noInit t                             = predh "NoInit" [introduced t]

select r f t                         = predh "Select" [introduced r, introduced (TyLabel f), t]
selectBranch datatype branch field t = select (bitdataCase datatype branch) field t
selectFails r f t                    = predf "Select" (map introduced [r, f, t])

update r lab                         = predh "Update" (map introduced [r, TyLabel lab])
updateBranch datatype branch field   = update (bitdataCase datatype branch) field
updateFails r f                      = predf "Update" (map introduced [r, f])

-- Quill predicates

unrestricted t                       = predh "Un" [t]
lesserRestricted t u                 = predh ">:=" [t, u]
fun t                                = predh "->" [t]
sepFun t                             = predh "SeFun" [t]
shFun t                              = predh "ShFun" [t]

xforall = X.Forall [] []
xgen   = X.Gen [] []

-- Construct an XMPEG expression for a structure initializer.  The first Ty argument is the
-- structure type, the two lists are matching sequences of initializer types and expressions.
structInit :: Ty -> [Ty] -> [X.Expr] -> X.Expr
structInit ty ts es
  = foldl X.EApp (X.ELetVar (X.Inst "primStructInit" (map convert (ty:ts)) [])) es -- TODO: revisit

----------------------------------------------------------------------------------------------------
-- Utility functions: environment variables

-- FIXME
freeEnvironmentVariables :: M [KId]
freeEnvironmentVariables =
    do s  <- gets currentSubstitution
       ts <- gets (Map.elems . typeEnvironment)
       return (nub (tvs (s ## (map (\(bnds, _, _) -> bnds) ts))))

-- splitPredicates: predicates -> (retained, deferred)
splitPredicates :: Preds -> M (Preds, Preds)
splitPredicates [] = return ([], [])
splitPredicates preds =
    do envvars <- freeEnvironmentVariables
       ps' <- substitute ps
       fds <- inducedDependencies ps
       let envvars' = close envvars fds
           mustRetain (_, p) = any (`notElem` envvars') (tvs p)
           (retained, deferred) = partition mustRetain (zip vs ps')
       trace ("With  environment variables " ++ intercalate ", " (map (show . ppr) envvars) ++
              "\n  retained predicates\n" ++ unlines ["    " ++ show (ppr id <::> ppr p) | (id, p) <- retained] ++
              "  and deferred predicates\n" ++ unlines ["    " ++ show (ppr id <::> ppr p) | (id, p) <- deferred])
             (return (retained, deferred))
    where (vs, ps) = unzip preds

contextTooWeak :: Preds -> Preds -> M ()
contextTooWeak assumed goals =
    failWith (shorten (map snd (assumed ++ goals)) $
              hang 4 ("Cannot prove" <+> pprList' (map snd assumed) <+> "=>" </> pprList' (map snd goals) <$$>
                      text "arising at" <+> pprList [loc | At loc _ <- map snd goals]))

----------------------------------------------------------------------------------------------------
-- Utility functions: functional dependencies

inducedDependencies :: [Located (Pred (Located Ty))] -> M [Fundep KId]
inducedDependencies locPs =
    do allDependencies <- gets (functionalDependencies . classEnvironment)
       return (concatMap (fundeps' allDependencies) ps)
    where ps = map dislocate locPs
          fundeps' _ (Pred className ts Fails) = []
          fundeps' allDependencies (Pred className ts Holds) = map replace classDependencies
              where classDependencies = fromMaybe [] (Map.lookup className allDependencies)
                    replace (xs :~> ys) = nub (tvs (map (ts !!) xs)) :~> nub (tvs (map (ts !!) ys))

close :: [KId] -> [Fundep KId] -> [KId]
close vars fds
    | vars == next = vars
    | otherwise    = close next fds
    where next = nub (concatMap step fds ++ vars)
          step (xs :~> ys)
              | all (`elem` vars) xs = ys
              | otherwise            = []

----------------------------------------------------------------------------------------------------
-- Utility functions: improvement and type schemes

kindQuantify :: TyS -> KScheme TyS
kindQuantify tys@(Forall kids (_ :=> At _ ty)) = ForallK kvars tys
    where kvars = concatMap (K.vars . kind) kids ++ K.vars (kindOfGen kids ty)

quantify :: [KId] -> QTy -> KScheme TyS
quantify vars qty@(_ :=> At _ ty) = kindQuantify (Forall vars (gen 0 vars qty))

simplifyScheme :: KScheme TyS -> M (KScheme TyS)
simplifyScheme tys =
    do (_, _, qs :=> t) <- instantiate tys
       evvars   <- freshFor "e" qs
       envvars  <- freeEnvironmentVariables
       (_, qs', _) <- trace (show ("Simplifying scheme" <+> ppr tys)) $
                      solve (tvs t ++ envvars) (tvs t) (zip evvars qs)
       qty <- substitute (map snd qs' :=> t)
       -- This last line breaks scoped type variables: if some of the variables in qty had
       -- been scoped before, they're not afterwards.  To fix: capture the list of new
       -- variables returned from instantiate, then intersect the tvs of qty with that
       -- list in the quantify call below.
       return (quantify (tvs qty) qty)

----------------------------------------------------------------------------------------------------
-- Bitdata field and structure region operations

fieldType                       :: BitdataField KId -> M (Located Ty)
fieldType (LabeledField n t ini) = return t
fieldType (ConstantField (At _ lit))
    = case lit of
        BitVector n w -> return (introduced (bitTy @@ TyNat (fromIntegral w)))
        Numeric n     -> do w <- fresh "width"
                            return (introduced (bitTy @@ TyVar (Kinded w KNat)))

sizeDetermined (At _ (TyApp (At _ (TyCon (Kinded "Bit" (KFun KNat KStar))))
                            (At _ (TyVar _)))) = False
sizeDetermined _                               = True


----------------------------------------------------------------------------------------------------
-- Utility functions: output

-- Return the list of elements that appear multiple times in the input list:
duplicates       :: Eq a => [a] -> [a]
duplicates []     = []
duplicates (a:as)
  | a `elem` as   = a : duplicates (filter (a/=) as)
  | otherwise     = duplicates as

-- Convert a non-empty list of Id's into a comma separated list:
commaSep :: [Id] -> String
commaSep  = intercalate ", " . map fromId

-- Generate a message with a number followed by a trailing singular or plural noun:
multiple            :: (Show a, Eq a, Num a) => a -> String -> String -> String
multiple n sing plur = show n ++ " " ++ if n==1 then sing else plur

-- Generate short names, as available, for each variable in a type.
shorten :: HasTypeVariables t KId => t -> Doc -> Doc
shorten t d = iter (tvs t)
    where iter (v:vs) = bindingTyVar v (const (iter vs))
          iter []     = d
