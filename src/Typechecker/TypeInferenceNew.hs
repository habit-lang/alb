{-# LANGUAGE NoOverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, StandaloneDeriving, UndecidableInstances, FlexibleInstances #-}
module Typechecker.TypeInferenceNew (inferTypes, Binding(..), to, (@@), doTrace) where

import Common
import Control.Monad.State
import Data.Map (Map)
import Data.List
import Data.Ord
import qualified Data.Map as Map
import Solver (SolverEnv)
import Syntax.Common
import Syntax.IMPEG
import qualified Syntax.IMPEG.KSubst as K
import Syntax.IMPEG.TSubst hiding (unify)
import qualified Syntax.XMPEG as X
import Printer.Common
import Data.Maybe

import Typechecker.TypeInference.Base hiding (trace, M, TcState, expect, matches, unifies, instantiate, substitute, runM, inducedDependencies)
import qualified Typechecker.TypeInference.Base as Base
import Typechecker.TypeInference.Expr
import Typechecker.TypeInference.TopDecl as TopDecl

import Debug.Trace
import Printer.Common

----------------------------------------------------------------------------------------------------

{-
data TcState     = TcState { typeEnvironment     :: TyEnv
                           , ctorEnvironment     :: CtorEnv
                           , classEnvironment    :: ClassEnv
                           , genericVars         :: ([KId], [Id])
                           , currentSubstitution :: Unifier
                           , bitdataCtors        :: BitdataCtorEnv
                           , structRegions       :: StructRegionEnv }
-}

-- Things that may change and that need to be updated globally when they do
data TcState = TcState {
  uniVar2BubbleId :: Map.Map UniVar BubbleId,
  bubbleId2Bubble :: Map.Map BubbleId Bubble,

  instantiations :: [(BubbleId, Ty, VarEnvBinding)],
  --varEnv :: VarEnv, -- TODO: Not actually VarEnv b/c VarEnv is reader not state.  But we do need a map from the co-domain of VarEnv to the current generalization
  --  Var -> ???
  unifications :: [(BubbleId, Ty, Ty)],
  unificationsWithEqvt :: [(BubbleId, Ty, Ty)],
  unifier :: Unifier, -- Unifications that are unequivically done
  --rootwards :: [...],
  --leafwards :: [...],
  ctorEnv :: CtorEnv
} deriving (Show)

type VarEnv = Map.Map Var VarEnvBinding
data VarEnvBinding = PlainBinding Ty | ExplicitBinding (KScheme (Scheme Pred KId)) | GeneralizedBinding BubbleId Ty deriving (Show)

instance Printable VarEnvBinding where
  ppr (PlainBinding ty) = text "[" <+> ppr ty <+> text "]"
  ppr (ExplicitBinding ty) = text "{" <+> ppr ty <+> text "}"
  ppr (GeneralizedBinding (BubbleId b) ty) = text "(" <+> ppr b <+> text "|" <+> ppr ty <+> text ")"

data Bubble = Bubble {
  bubble_id :: BubbleId,
  parent :: BubbleId,
  --children :: [BubbleId], -- derived after all bubbles created
  popped :: Bool
  --constraint_leakage :: Maybe (Preds) -- If nothing, then leaks nothing.  Otherwise, leaks all but those in the Preds
  --stalled_lam ::
  --stalled_var ::
  --generalizations :: [(Var, TODO)]
--  stalled :: [(UniVar {-untouchable-}, Type UniVar)], {- May be caused by lambda -}
--  generalizations :: [(Var, UniVar)]
} deriving (Show)

newtype M t = M { runM :: StateT TcState Base t }
    deriving (Functor, Applicative, Monad, MonadBase, MonadState TcState)

say :: (Monad m) => String -> m ()
say x = trace x $ return ()

bubbleChildren b bubbles = [(b_id,b_v) | (b_id,b_v) <- bubbles, parent b_v == b]

type TcPassState = (ClassEnv, TyEnv, CtorEnv, BitdataCtorEnv, BitdataBDDEnv, StructRegionEnv, [RequirementT])
inferTypes :: String -> Pass TcPassState (Program Pred KId KId) (X.Program KId, (Map Id (X.Scheme X.Type, Int), SolverEnv))
inferTypes fn p = PassM (StateT (\globals@(classEnv, tyEnv, ctorEnv, bitdataCtors, bitdataBDDs, structRegions, rqts) -> do
  trace (show (ppr p)) $ return ()
  ((ctorEnv, methodEnv),_) <- runStateT (Base.runM (do
       ctorEnv <- liftM Map.unions $ mapM buildCtorEnv (topDecls p)
       methodEnv <- liftM Map.unions $ mapM buildMethodEnv (topDecls p)
       return (ctorEnv, methodEnv)))
    (Base.TcState tyEnv ctorEnv classEnv ([], []) emptyUnifier [] bitdataCtors bitdataBDDs structRegions rqts)

  b00 <- liftM BubbleId $ fresh (fromString "b00")
  let env0 = methodEnv
  (_, finalState) <- runStateT (runM (local_bubble b00 (\b0 -> make_bubbles_decls b0 env0 (decls p) (const (return ())))))
    (TcState { uniVar2BubbleId = Map.empty, bubbleId2Bubble = Map.empty,
               unifier = emptyUnifier, instantiations = [], unifications = [], unificationsWithEqvt = [], ctorEnv = ctorEnv})
  let bubbles = Map.toList (bubbleId2Bubble finalState)
  let varBubbles = Map.toList (uniVar2BubbleId finalState)
  let instantiations' = instantiations finalState
  let unifications' = unifications finalState
  let unificationsWithEqvt' = unificationsWithEqvt finalState
  let showBubble prefix (id, b) =
        prefix++"+"++show id++"\n"++
        --prefix++"  Parent = "++show (parent b)++"\n"++
        concat [prefix++"  "++show x++"\n" | (x,b') <- varBubbles, id == b']++
        concat [prefix++"  "++show (ppr t1)++"=="++show (ppr t2)++"\n" | (b',t1,t2) <- unifications', id == b'] ++
        concat [prefix++"  "++show (ppr t1)++"~~"++show (ppr t2)++"\n" | (b',t1,t2) <- unificationsWithEqvt', id == b'] ++
        concat [prefix++"  "++show (ppr t)++"<="++show (ppr binding)++"\n" | (b',t,binding) <- instantiations', id == b'] ++
        concatMap (showBubble ("  "++prefix)) (bubbleChildren id bubbles)
  --say "Bubbles:\n"
  --mapM_ (say . showBubble) bubbles
  mapM_ (say . showBubble "") (bubbleChildren b00 bubbles)
  say (show (unifier finalState))
  --say (show ctorEnv)
  --say (show methodEnv)

{-
  unifier :: Unifier -- Unifications that are unequivically done
  --rootwards :: [...],
  --leafwards :: [...],
-}

  error "END NEW TYPE INFERENCE"))

newTyVarAnon :: BubbleId -> String -> M Ty
newTyVarAnon b x = do
  v <- fresh (fromString x)
  modify (\s -> s { uniVar2BubbleId = Map.insert (Kinded v KStar) b (uniVar2BubbleId s) })
  return (TyVar (Kinded v KStar))

newTyVarName :: BubbleId -> Id -> M Ty
newTyVarName b x = do
  v <- fresh x
  modify (\s -> s { uniVar2BubbleId = Map.insert (Kinded v KStar) b (uniVar2BubbleId s) })
  return (TyVar (Kinded v KStar))

addBinding :: Var -> Ty -> VarEnv -> VarEnv
addBinding v t e = Map.insert v (PlainBinding t) e

addExplicitBinding :: Var -> (KScheme (Scheme Pred KId)) -> VarEnv -> VarEnv
addExplicitBinding v t e = Map.insert v (ExplicitBinding t) e

addGeneralization :: Var -> BubbleId -> Ty -> VarEnv -> VarEnv
addGeneralization v b t e = Map.insert v (GeneralizedBinding b t) e

newtype BubbleId = BubbleId Id deriving (Show, Eq, Ord)
newtype GeneralizationId = GenId Id deriving (Show, Eq, Ord)
type UniVar = KId
type Var = Id

instantiate :: BubbleId -> VarEnv -> Ty -> Var -> M ()
instantiate b env t v =
  case Map.lookup v env of
    Just binding -> modify (\s -> s { instantiations = (b, t, binding) : instantiations s })
    Nothing -> trace ("UNBOUND:"++show v) (return ())
-- Constructor
-- Method

instantiateCtor :: BubbleId -> Ty -> Var -> M ()
instantiateCtor b t c = do
  env <- gets ctorEnv
  case Map.lookup c env of
    Just (binding, 0) -> modify (\s -> s { instantiations = (b, t, ExplicitBinding binding) : instantiations s })
    Just _ -> trace ("UNIMPLEMENTED:"++show c) (return ())
    Nothing -> trace ("UNBOUND:"++show c) (return ())

instantiatePCon :: BubbleId -> Ty -> Var -> M ()
instantiatePCon b t x = trace ("UNIMPLEMENTED: instantiatePCon "++show (b, t, x)) (return ())

unify :: BubbleId -> Ty -> Ty -> M ()
unify b t1 t2 = modify (\s -> s { unifications = (b, t1, t2) : unifications s })

unifyEqvt :: BubbleId -> Ty -> Ty -> M ()
unifyEqvt b t1 t2 = modify (\s -> s { unificationsWithEqvt = (b, t1, t2) : unificationsWithEqvt s })

make_bubbles_typing_group b env (Explicit (lhs, args, match) t@(ForallK local_kinds (Forall local_types (preds :=> (At _ typ))))) cont = do
  let env' = addExplicitBinding lhs t env -- WithScheme
  local_bubble b (\b' -> do
    args' <- mapM (newTyVarName b') args
    ret' <- newTyVarAnon b' "r_e"
    unify b' (foldr to ret' args') typ
    make_bubbles_match b' (foldr (uncurry addBinding) env' (zip args args')) ret' match)
  --TODO: add preds to leafwards set
  cont env'
make_bubbles_typing_group b env (Implicit funcs) cont = local_bubble b go where
  go b' = do
    binds <- sequence [newTyVarName b' lhs >>= return . ((,) lhs) | (lhs, _, _) <- funcs]
--mapM (newTyVarName b' . fst3) funcs
    let env' = foldr (uncurry addBinding) env binds
    mapM (go' env') (zip funcs binds)
    cont (foldr generalize env binds) {- NOTE: this is env not env' -} where
      fst3 (x, _, _) = x
      generalize (lhs, lhs') env = addGeneralization lhs b lhs' env
      go' env' ((lhs, args, match), (_, lhs')) = do
        args' <- mapM (newTyVarName b') args
        ret' <- newTyVarAnon b' "r_e"
        unify b' (foldr to ret' args') lhs'
        make_bubbles_match b' (foldr (uncurry addBinding) env' (zip args args')) ret' match
make_bubbles_decls b env (Decls { groups = [] }) cont = cont env
make_bubbles_decls b env (Decls { groups = (g : gs) }) cont = do
  make_bubbles_typing_group b env g (\env' ->
    make_bubbles_decls b env' (Decls { groups = gs }) cont)

make_bubbles_expr :: BubbleId{-current bubble-} -> VarEnv -> Ty{-expected type-} -> Expr Pred KId -> M ()
make_bubbles_expr b env t (ELet ds (At _ e)) =
  make_bubbles_decls b env ds (\env' -> make_bubbles_expr b env' t e)
make_bubbles_expr b env t (ELam x (At _ e)) = do
  -- TODO: do we need to use the type equality rules here?
  -- TODO: could we get stalled unifications here?
  x' <- newTyVarName b x
  r' <- newTyVarAnon b "r_l"
  unifyEqvt b t (x' `to` r')
  make_bubbles_expr b (addBinding x x' env) r' e
make_bubbles_expr b env t (EVar x) = do
  instantiate b env t x
make_bubbles_expr b env t (ECon c) = do
  instantiateCtor b t c
--make_bubbles_expr (EBitCon Id [(Id, Located (Expr p tyid))])
--make_bubbles_expr (EBits Integer Int)
make_bubbles_expr b env t (EMatch m) = make_bubbles_match b env t m
make_bubbles_expr b env t (EApp (At _ e1) (At _ e2)) = do
  f <- newTyVarAnon b "f"
  a <- newTyVarAnon b "a"
  unify b f (a `to` t)
  make_bubbles_expr b env f e1
  make_bubbles_expr b env a e2
--make_bubbles_expr (EBind Id (Located (Expr p tyid)) (Located (Expr p tyid)))
--make_bubbles_expr (EStructInit Id [(Located Id, Located (Expr p tyid))])
--make_bubbles_expr b e = error $ "unsupported construct: " ++ (show (ppr e))

make_bubbles_match b env t (MFail) = return ()
make_bubbles_match b env t (MCommit (At _ e)) = make_bubbles_expr b env t e
make_bubbles_match b env t (MElse m1 m2) =
  make_bubbles_match b env t m1 >> make_bubbles_match b env t m2
make_bubbles_match b env t (MGuarded g m) =
  make_bubbles_guard b env g (\b' env' -> make_bubbles_match b' env' t m)

make_bubbles_guard :: BubbleId -> VarEnv -> Guard Pred KId -> (BubbleId -> VarEnv -> M ()) -> M ()
make_bubbles_guard b env (GFrom (At _ p) (At _ e)) cont = do
  pt <- newTyVarAnon b "p"
  make_bubbles_expr b env pt e
  make_bubbles_pattern b env pt p cont
--make_bubbles_guard b env (GLet decls) cont = error "make_bubbles_guard decls"

make_bubbles_pattern :: BubbleId -> VarEnv -> Ty -> Pattern Pred KId -> (BubbleId -> VarEnv -> M ()) -> M ()
make_bubbles_pattern b env pt (PWild) cont = cont b env
make_bubbles_pattern b env pt (PVar v) cont = do
  v' <- newTyVarName b v
  unify b pt v'
  cont b (addBinding v v' env)
make_bubbles_pattern b env pt (PCon ctor xs) cont = do
  --(tys, n) <- ctorBinding ctor -- TODO: what is "n"?  It seems related to existentials.
  --instantiate b/b' pt tys_res
  --tys' <- freshen tys
  --instantiate b pt
  local_bubble b (\b' -> do
    -- This odd incantation is so that the result type of the ctor
    -- effects outside the bubble, but the argument types do not.
    -- This might not be nessisary.
    xs_outside <- mapM (newTyVarName b) xs
    instantiateCtor b (foldr to pt xs_outside) ctor
    xs_inside <- mapM (newTyVarName b') xs
    mapM (uncurry (unify b')) (zip xs_outside xs_inside)
    --instantiatePCon b (foldr to pt xs') ctor -- NOTE: this is "b" not "b'"
    let env' = foldr (uncurry addBinding) env (zip xs xs_inside)
    cont b' env')
-- TODO: add qualifiers to leafwards set
make_bubbles_pattern b env pt (PGuarded p g) cont = do
  make_bubbles_pattern b env pt p (\b' env' -> make_bubbles_guard b' env' g cont)

local_bubble :: BubbleId -> (BubbleId -> M a) -> M a
local_bubble b m = do
  b' <- liftM BubbleId $ fresh (fromString "b")
  modify (\s -> s { bubbleId2Bubble = Map.insert b' (Bubble { bubble_id = b', parent = b, popped = False }) (bubbleId2Bubble s) })
  m b'

buildMethodEnv :: Located (TopDecl Pred KId KId) -> Base.M VarEnv
buildMethodEnv (At _ classDecl@(Class {})) = do
  (methodEnv, _, _)<- TopDecl.assertClass classDecl
  return $ Map.fromList [(name, ExplicitBinding sig) | (name, LetBound sig) <- Map.toList methodEnv]
buildMethodEnv _ = return Map.empty

buildCtorEnv :: Located (TopDecl Pred KId KId) -> Base.M CtorEnv
buildCtorEnv (At _ d@(Datatype {})) = do
  (_, env) <- TopDecl.checkTopDecl d
  return env
buildCtorEnv _ = return Map.empty

{-
(Kinded name k) ps ctors _)) = do
  ctors' <- mapM (simplifyCtor ps') ctors
  let ctorEnv = [ (ctorName, (kindQuantify (Forall (ks ++ map kind ps')
                                                     (gen (length ks) ps' (qs :=> introduced (map dislocate ts `allTo` t)))),
                              length ks))
                  | Ctor (At _ ctorName) ks qs ts <- ctors' ]
  return ctorEnv where
    ps'       = map dislocate ps
    t         = foldl (@@) (TyCon (Kinded name k)) (map TyVar ps')
-}

{-
simplifyCtor :: (K.HasKinds t, HasTypeVariables t KId) => [KId] -> Ctor (PredType Pred KId) t -> M (Ctor (PredType Pred KId) t)
simplifyCtor univs (Ctor id@(At l _) ks ps0 t) =
    failAt l $
    do tyIds <- freshFor (fromString "t") ks
       let kids = zipWith Kinded tyIds ks
           ts = map TyVar kids
           ps1 = inst ts ps0
           t' = inst ts t
           (ps2, qs) = partition (all (`elem` kids) . tvs) ps1
       evvars <- freshFor (fromString "e") ps2
       (s, _, ps3, _) <- entails' (tvs t) (tvs t) [] (zip evvars ps2)
       let ps4 = s ## (map snd ps3 ++ qs)
           t'' = s ## t'
           kids' = kids `intersect` (concatMap tvs ps4 ++ tvs t'')
       fds <- inducedDependencies ps4
       when (not (null (kids' \\ close univs fds)))
            (failWithS "Unsupported existential type in constructor")
       return (Ctor id (map kind kids') (gen 0 kids' ps4) (gen 0 kids' t''))

inducedDependencies :: [Located (Pred (Located Ty))] -> M [Fundep KId]
inducedDependencies locPs =
    do allDependencies <- gets (functionalDependencies . classEnvironment)
       return (concatMap (fundeps' allDependencies) ps)
    where ps = map dislocate locPs
          fundeps' _ (Pred className ts Fails) = []
          fundeps' allDependencies (Pred className ts Holds) = map replace classDependencies
              where classDependencies = fromMaybe [] (Map.lookup className allDependencies)
                    replace (xs :~> ys) = nub (tvs (map (ts !!) xs)) :~> nub (tvs (map (ts !!) ys))
-}

deriving instance (Show tyid, Show (p (Located (Type tyid)))) => Show (Qual (PredType p tyid) (Type tyid))
deriving instance (Show (p (Located (Type tyid))), Show tyid) => Show (Scheme p tyid)
deriving instance (Show ty) => Show (Pred ty)

-----


------------------------------------
-- DEAD CODE ONLY BELOW THIS LINE --
------------------------------------

{-
substitute :: (K.HasKinds t, HasTypeVariables t KId, MonadState TcState m) => t -> m t
substitute t = do s <- gets unifier
                  return (s ## t)

expect :: (Unifies t, Printable t) => (([KId], [Id]) -> t -> t -> Either String Unifier) -> t -> t -> M Unifier
expect f expected actual =
    do --gvars     <- gets genericVars
       expected' <- substitute expected
       actual'   <- substitute actual
       case f ([], [{-TODO-}]) expected' actual' of
         Left err -> failWith (withShowKinds True $
                               align (text "Type error:" <+> text err <$>
                                       text "Expected:  " <+> ppr expected'  <$>
                                       text "Found:     " <+> ppr actual'))
         Right u  -> do modify (\st -> st { {-typeEnvironment = applyToEnvironment u (typeEnvironment st)
                                          , -} unifier = u `composeU` unifier st })
                        traceIf (not (isEmpty (snd u)))
                                (show (text "Unification: expected" <+> ppr expected' <> text ", found" <+> ppr actual' <$>
                                       --"Generic:" <+> cat (punctuate ", " (map ppr (fst gvars))) <$>
                                       text (substStr (snd u))))
                                (return u)

unifies, matches :: (Unifies t, Printable t) => t -> t -> M Unifier
unifies = expect unify
matches = expect match
-}

--make_bubbles_expr b t (ELet (Decls []) (At _ e)) = make_bubbles_expr b t e
-- TODO: what is ForallK?
{-
make_bubbles_expr b t (ELet (Decls (((Explicit (lhs, args, match)) (ForallK _ (Forall kinds (preds :=> (At _ typ))))) : ds)) body) = do
--  TODO
  local_bubble b (\b' -> make_bubble_match b' ... match)
  make_bubble_expr b t (ELet (Decls ds) body)
--make_bubbles_expr b t (ELet (Decls ((Implicit (Functions p tyid)) : ds)) (At _ e)) = do
--  TODO
-}

-- Originally I thought I could extract the underlying "case" structure from MPEG
-- but now that seems too hard.
{-
make_bubbles_expr b t (EMatch m)
  | Just (e, alts) <- isCase m = do
  s <- newTyVarAnon "s"
  make_bubbles_expr b s e
  mapM_ (make_bubbles_alt b t s) alts

make_bubbles_alt :: BubbleId -> Ty{-ret type-} -> Ty{-scrut type-} -> (Pattern Pred KId, Expr Pred KId) -> M ()
make_bubbles_alt b t s (PWild, rhs) = do
  make_bubbles_expr b t rhs
make_bubbles_alt b t s (PVar x, rhs) = do
  x' <- newTyVarName x
  unifies s x'
  make_bubbles_expr b t rhs
--make_bubbles_alt b t s (PCon ctor xs, rhs) = do
--  xs' <- mapM newTyVarName xs
--  unifies (ctor xs') s
--  local_bubble b (\b' -> make_bubbles_expr b' t rhs)
--make_bubbles_pat (PTyped (Located (Pattern p tyid)) (Scheme p tyid))
--make_bubbles_pat (PGuarded (Pattern p tyid) (Guard p tyid)
-}



{-
                                 do ((p', xctors, tyEnv'), TcState _ ctorEnv' classEnv' _ _ bitdataCtors' structRegions') <-
                                        runStateT (runM (checkProgram fn p))
                                                      (TcState tyEnv ctorEnv classEnv ([], []) emptyUnifier bitdataCtors structRegions)
                                    return ((p', (xctors, solverEnvironment classEnv')),
                                            (classEnv', Map.union tyEnv tyEnv', ctorEnv', bitdataCtors', structRegions'))))
-}


{-
          -- if cond cons alt is rewritten to the match { True <- cond => ^cons | ^alt }; note that
          -- we're (now) avoiding the unnecessary check for False in the alternative branch.
          desugar (S.EIf (S.ScExpr cond) cons alt) =
              do cond' <- desugar cond
                 cons' <- desugar cons
                 alt' <- desugar alt
                 name <- fresh "condition"
                 return (EMatch (MGuarded (GFrom (introduced (PVar name)) cond')
                                 ((MGuarded (gfrom (PCon "True" ["$true"]) (EVar name)) (MCommit cons')) `MElse`
                                  (MCommit alt'))))
-}

{-
isIf (EMatch (MGuarded (GFrom (introduced (PVar name)) cond')
                                 ((MGuarded (gfrom (PCon "True" ["$true"]) (EVar name)) (MCommit cons')) `MElse`
                                  (MCommit alt')))) =
-}

{-
          -- We begin a case by binding the scrutinee to a new value; this avoids recomputing it for
          -- each guard in the match.
          desugar (S.ECase (S.ScExpr scrutinee) alts) =
              do name <- fresh "scrutinee"
                 scrutinee' <- desugar scrutinee
                 alts' <- foldl1 MElse `fmap` mapM (desugarAlt name) alts
                 return (EMatch (MGuarded (GFrom (introduced (PVar name)) scrutinee') alts'))
              where -- Alternative may bind new names.  We begin by constructing replacements for
                    -- any bound names that would shadow existing definitions; after this,
                    -- desugaring the alternative is straightforward.
                    desugarAlt name (p S.:-> rhs) =
                        do p'@(At l _) <- desugar p
                           rhs' <- desugar rhs
                           return (MGuarded (GFrom p' (At l (EVar name))) rhs')
-}

{-
isAlt :: Id -> Match Pred KId -> Maybe (Pattern Pred KId, Expr Pred KId)
isAlt n (MGuarded (GFrom (At _ p') (At _ (EVar name))) (MCommit (At _ rhs'))) | n == name = Just (p', rhs')
isAlt _ _ = Nothing

isAlts n (MElse alt' alts') = liftM2 (:) (isAlt n alt') (isAlts n alts')
isAlts n e | Just (p, rhs) <- isAlt n e = Just [(p, rhs)]
isAlts _ _ = Nothing

isCase (MGuarded (GFrom (At _ (PVar name)) (At _ scrutinee')) alts')
  | Just alts <- isAlts name alts' = Just (scrutinee', alts)
isCase _ = Nothing
-}

{-

          -- The majority of the work for ELam is actually handled by desugarParameterList (defined
          -- far below) which handles the details of desugaring patterns and introducing new
          -- parameter names when necessary.
          desugar (S.ELam patterns body) =
              do (args', body') <- desugarParameterList patterns (MCommit `fmap` desugar body)
                 return (dislocate (foldr elam (introduced (EMatch body')) args'))
              where elam v body = introduced (ELam v body)

-}


{-
data Type id = TyCon id
             | TyVar id
             -- | TyGen Int -- quantified type variable
             | TyApp !(Located (Type id)) !(Located (Type id))
             -- | TyNat Integer
             -- | TyKinded (Located (Type id)) (Located Kind)
             -- | TyLabel Id
               deriving (Eq, Show)

data Expr p tyid
  = EVar Id
  | ECon Id
  | EApp (Located (Expr p tyid)) (Located (Expr p tyid))
  | ELet (Decls p tyid) (Located (Expr p tyid))
  | ELam Id (Located (Expr p tyid))
  | ECase Scrutinee [Alt]

data Scrutinee = ScExpr (Located Expr)
               | ScFrom (Located Expr)
               deriving Show

data Alt = Located Pattern :-> Rhs deriving Show

data Decls p tyid = Decls { groups :: [TypingGroup p tyid] } -- sorted by dependencies

type PredType pred tyid = pred (Located (Type tyid))
data Qual p t           = [Located p] :=> Located t
data Scheme p tyid      = Forall [Kind] (Qual (PredType p tyid) (Type tyid))
data TypingGroup p tyid = Explicit (Function p tyid) (KScheme (Scheme p tyid))
                        | Implicit (Functions p tyid)




data Signature p tyid = Signature Id (KScheme (Scheme p tyid))

type Function p tyid = (Id, [Id], Match p tyid)
type Functions p tyid = [Function p tyid]


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

-}
