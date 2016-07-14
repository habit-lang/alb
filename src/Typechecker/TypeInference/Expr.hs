{-# LANGUAGE FlexibleContexts #-}

module Typechecker.TypeInference.Expr where

import Prelude hiding ((<$>))

import Common
import Control.Monad
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Printer.Common hiding (empty)
import Syntax.Common
import Syntax.IMPEG
import qualified Syntax.IMPEG.KSubst as K
import Syntax.IMPEG.TSubst
import qualified Syntax.XMPEG as X
import qualified Syntax.XMPEG.TSubst as X
import Typechecker.TypeInference.Base

----------------------------------------------------------------------------------------------------

checkExpr :: Located Exp -> Ty -> TcRes X.Expr

checkExpr (At loc (ELet ds body)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do R (ds', vals) assumed ps usedDefn <- checkDecls ds
       R body' assumed' qs usedBody <- binds loc vals (checkExpr body expected)
       (assumedC, goalsC, used) <- contract loc usedDefn usedBody
       return R{ payload = X.ELet ds' body'
               , assumed = assumed ++ assumed' ++ assumedC
               , goals = ps ++ qs ++ goalsC
               , used = used}

checkExpr (At loc (ELam var body)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do argTy@(TyVar arg) <- newTyVar KStar
       resTy             <- newTyVar KStar
       (funp, t)         <- argTy `polyTo` resTy
       unifies expected t
       r <- bind loc var (LamBound argTy) (checkExpr body resTy)
       (gteAssumps, gteGoals) <- unzip `fmap` mapM (buildLinPred loc (flip moreUnrestricted (At loc t)) <=< bindingOf) (used r)
       traceIf (not (null gteGoals))
               (show ("In function" <+> ppr (ELam var body) <+> "used" <+> pprList' (used r) <$>
                      "giving entailment" <+> pprList' (map snd (concat gteAssumps)) <+> "=>" <+> pprList' (map snd gteGoals)))
               (return r{ payload = X.ELam var (X.TyVar arg) (payload r)
                        , assumed = concat gteAssumps ++ assumed r
                        , goals = funp : gteGoals ++ goals r })

checkExpr (At loc (EVar name)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected <+> "for variable" <+> ppr name)) $
    do b <- bindingOf name
       case b of
         LamBound ty ->
             do unifies expected ty
                return R{ payload = X.ELamVar name
                        , assumed = []
                        , goals = []
                        , used = [name] }
         LetBound tys ->
             do (kvars, kids, ps :=> At _ ty) <- instantiate tys
                unifies expected ty
                evNames <- freshFor "e" ps
                let preds = zip evNames [At loc p | At _ p <- ps]
                trace (show (hang 4 (text "At" <+> ppr loc <$>
                                     ppr name <+> text "gets type" <+> ppr ty <$>
                                     text "and introduces" <$>
                                     vcat [ppr id <::> ppr p | (id, p) <- preds])))
                      (return R{ payload = X.ELetVar (X.Inst name (map X.TyVar kids) (map X.EvVar evNames))
                               , assumed = []
                               , goals = preds
                               , used = [name] })

checkExpr (At loc (ECon name)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do b <- bindingOf name
       case b of
         LamBound _ -> error "Constructor name associated with lambda-bound type"
         LetBound tys ->
             do (kvars, kids, ps :=> At _ ty) <- instantiate tys
                unifies expected ty
                evNames <- freshFor "e" ps
                return R{ payload = X.ECon (X.Inst name (map X.TyVar kids) (map X.EvVar evNames))
                        , assumed = []
                        , goals = zip evNames [At loc p | At _ p <- ps]
                        , used = []}

checkExpr (At loc (EBitCon ctor fs)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do -- Check that there are no duplicates in the list of named fields:
       let fsNames = [ id | (id, _) <- fs ]
           dups    = duplicates fsNames
       when (not (null dups)) $
         failWithS ("Multiple values for " ++ commaSep dups)

       -- Lookup information about the fields for this constructor:
       (ty, fields) <- gets (fromMaybe (error ("Unknown bitdata ctor " ++ fromId ctor)) .
                             Map.lookup ctor .
                             bitdataCtors)
       unifies expected ty
       let notFields = fsNames \\ [ n | (n, _, _) <- fields ]
       when (not (null notFields)) $
         failWithS ("There are no fields called " ++ commaSep notFields ++ " for constructor " ++ fromId ctor)

       -- Compute full list of field values using default initial values where necessary:
       rFields <- mapM fieldFor fields
                  -- (es', pss) <- unzip `fmap` mapM fieldFor fields
       (assumedC, goalsC, used) <- contractMany loc (map used rFields)
       let cty  = [ t | (_, t, _) <- fields ] `allTo` (bitdataCaseTy @@ ty @@ TyLabel ctor)
           prim = X.ELetVar (X.Inst "constructBitdata" [convert cty] [])
           cons = X.ECon (X.Inst ctor [] []) -- constructor is monomorphic
       return R{ payload = X.EApp cons (foldl X.EApp prim (map payload rFields))
               , assumed = assumedC ++ concatMap assumed rFields
               , goals = goalsC ++ concatMap goals rFields
               , used = used }

    where fieldFor :: (Id, Ty, Maybe Id) -> TcRes X.Expr
          fieldFor (fieldName, fieldTy, defaultId) =
              case lookup fieldName fs of
                Just e ->
                    checkExpr e fieldTy -- can only substitute for variables in ty'; this ensures
                                        -- that the value is at least as polymorphic as the field
                                        -- type.  The big need for this is in literal types,
                                        -- which are still fairly polymorphic.
                Nothing ->
                    case defaultId of
                      Nothing -> failWithS ("Uninitialized field " ++ fromId fieldName)
                      Just id -> return R{ payload = X.ELetVar (X.Inst id [] [])
                                         , assumed = []
                                         , goals = []
                                         , used = [id] }

checkExpr (At loc (EBits value size)) expected =
    do unifies expected (bitTy @@ TyNat (fromIntegral size))
       return R{ payload = X.EBits value size
               , assumed = []
               , goals = []
               , used = [] }

checkExpr (At loc (EMatch m)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do r <- checkMatch m expected
       return r{ payload = X.EMatch (payload r) }

checkExpr (At loc (EApp f a)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do t <- newTyVar KStar
       (funp, fty) <- t `polyTo` expected
       rF <- checkExpr f fty
       rA <- checkExpr a t
       (assumedC, goalsC, used) <- contract loc (used rF) (used rA)
       return R{ payload = X.EApp (payload rF) (payload rA)
               , assumed = assumedC ++ assumed rF ++ assumed rA
               , goals = funp : goalsC ++ goals rF ++ goals rA
               , used = used }

checkExpr (At loc (EBind v e rest)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do -- variables names are based on (>>=) :: m a -> (a -> m b) -> m b
       tya <- newTyVar KStar
       tyb <- newTyVar KStar
       tym <- newTyVar (KStar `KFun` KStar)
       unifies expected (tym @@ tyb)
       rE <- checkExpr e (tym @@ tya)   -- (e', ps)
       rRest <- bind loc v (LamBound tya) (checkExpr rest expected) -- (rest', qs)
       (assumedC, goalsC, used) <- contract loc (used rE) (used rRest)
       evar <- fresh "e"
       return R{ payload = X.EBind (convert tya) (convert tyb) (convert tym) (X.EvVar evar) v (payload rE) (payload rRest)
               , assumed = assumedC ++ assumed rE ++ assumed rRest
               , goals = (evar, At loc (procPred (At loc tym))) : goalsC ++ goals rE ++ goals rRest
               , used = used }

checkExpr (At loc (EStructInit name inits)) expected =
    failAt loc $
    trace (show ("At" <+> ppr loc <+> "expect type" <+> ppr expected)) $
    do -- Check that there are no duplicates in the list of named fields:
       let initNames = [ id | (At _ id, _) <- inits ]
           dups      = duplicates initNames
       when (not (null dups)) $
         failWithS ("Multiple initializers for fields called " ++ commaSep dups)

       -- Lookup information about the regions for this structure:
       (ty, regions) <- gets (fromMaybe (error ("Unknown struct name " ++ fromId name)) .
                              Map.lookup name .
                              structRegions)
       unifies expected (TyApp (At loc initTy) (introduced ty))
       let notFields = initNames \\ [ n | (Just n, _, _) <- regions ]
       when (not (null notFields)) $
         failWithS ("There are no fields called " ++ commaSep notFields ++ " for structure " ++ fromId name)

       -- Compute a full list of initializers for this structure:
       rRegionInits <- mapM initFor regions
       let (es, ts) = unzip (map payload rRegionInits)
       (assumedC, goalsC, used) <- contractMany loc (map used rRegionInits)
       return R{ payload = structInit ty ts es
               , assumed = assumedC ++ concat (map assumed rRegionInits)
               , goals = goalsC ++ concat (map goals rRegionInits)
               , used = used}

    where initFor :: (Maybe Id, Ty, Maybe Id) -> TcRes (X.Expr, Ty)
          initFor (mregName, regTy, mregInit)
            = case mregName of
                Nothing      ->  -- unnamed region, use default initializer
                  defaultInitializer
                Just regName ->  -- named field
                  case [ e | (At _ n, e) <- inits, n==regName ] of  -- look for used specified initializer
                    (e : _) ->
                      do rE <- checkExpr e initType -- confirm that initializer has correct type
                         return rE{ payload = (payload rE, initType) }
                    [] ->
                      case mregInit of -- look for an initializer in the structure definition
                        Just defInit -> return R{ payload = (X.ELetVar (X.Inst defInit [] []), initType)
                                                , assumed = []
                                                , goals = []
                                                , used = [] }
                        Nothing      -> defaultInitializer
              where
                initType = TyApp (At loc initTy) (At loc regTy)
                defaultInitializer :: TcRes (X.Expr, Ty)
                defaultInitializer  = do evar <- fresh "e"      -- evidence for Init ty
                                         return R{ payload = (X.EMethod (X.EvVar evar) 0 [] [], initType)
                                                 , assumed = []
                                                 , goals = [(evar, At loc (initablePred (At loc regTy)))]
                                                 , used = []}

----------------------------------------------------------------------------------------------------

checkMatch :: Match Pred KId -> Ty -> TcRes X.Match
checkMatch MFail expected =
    return R{ payload = X.MFail
            , assumed = []
            , goals = []
            , used = [] }
checkMatch (MCommit e) expected =
    do r <- checkExpr e expected
       return r{ payload = X.MCommit (payload r) }
checkMatch (MElse m n) expected =
    do rM <- checkMatch m expected
       rN <- checkMatch n expected
       (assumedC, goalsC, used) <- weakenBranching introducedLocation (used rM) (used rN)
       return R{ payload = X.MElse (payload rM) (payload rN)
               , assumed = assumedC ++ assumed rM ++ assumed rN
               , goals = goalsC ++ goals rM ++ goals rN
               , used = used }
checkMatch (MGuarded (GLet decls) m) expected =
    do rDecls <- checkDecls decls
       let (decls', vals) = payload rDecls
       rBody <- binds introducedLocation vals (checkMatch m expected)
       (assumedC, goalsC, used) <- contract introducedLocation (used rDecls) (used rBody)
       return R{ payload = X.MGuarded (X.GLet decls') (payload rBody)
               , assumed = assumedC ++ assumed rDecls ++ assumed rBody
               , goals = goalsC ++ goals rDecls ++ goals rBody
               , used = used }
checkMatch (MGuarded (GFrom (At l p) e) m) expected =
    do t <- newTyVar KStar
       case p of
         PWild ->
             do rExpr <- checkExpr e t -- (e', ps)
                rBody <- checkMatch m expected -- (m', qs)
                (assumedC, goalsC, used) <- contract introducedLocation (used rExpr) (used rBody)
                return R{ payload = X.MGuarded (X.GFrom X.PWild (payload rExpr)) (payload rBody)
                        , assumed = assumedC ++ assumed rExpr ++ assumed rBody
                        , goals = goalsC ++ goals rExpr ++ goals rBody
                        , used = used }
         PVar id ->
             do rExpr <- checkExpr e t
                rBody <- bind introducedLocation id (LamBound t) (checkMatch m expected)
                (assumedC, goalsC, used) <- contract introducedLocation (used rExpr) (used rBody)
                return R{ payload = X.MGuarded (X.GFrom (X.PVar id (convert t)) (payload rExpr)) (payload rBody)
                        , assumed = assumedC ++ assumed rExpr ++ assumed rBody
                        , goals = goalsC ++ goals rExpr ++ goals rBody
                        , used = used }
         PCon ctor vs ->
             do (tys, n) <- ctorBinding ctor
                (kvars, tyvars, ps :=> At _ t) <- instantiate tys
                let (parameters, result) = flattenArrows t
                    arity                = length parameters
                    valEnv               = Map.fromList (zip vs (map (LamBound . dislocate) parameters))
                when (length vs /= arity) $
                  failWithS (fromId ctor ++ " requires " ++ multiple arity "argument" "arguments")

                rExpr <- checkExpr e result

                evs <- freshFor "e" ps
                envvars <- freeEnvironmentVariables
                let ps'          = zip evs ps
                    transparents = tvs expected ++ tvs valEnv ++ envvars
                    ps''         = [(id, convert (dislocate p)) | (id, p) <- ps']
                    extVars      = take n tyvars

                rBody <- binds introducedLocation valEnv (checkMatch m expected)
                (evsubst, rs, cbindss) <-
                    traceIf (not (null (goals rBody)))
                            (show ("Simplifying predicates from guarded match:" <+> pprList' (map snd (goals rBody))))
                            (entails transparents (tvs expected ++ tvs valEnv) ps' (goals rBody))
--                extPreds <- existentialPredicates (take n tyvars) ps' (goals rExpr ++ rs) expected

                (assumedC, goalsC, used) <- contract introducedLocation (used rExpr) (used rBody)

                return R{ payload = X.MGuarded (X.GFrom (X.PCon ctor (map X.TyVar tyvars) ps'' vs) (payload rExpr))
                                               (foldr (\cbinds m -> case cbinds of
                                                                      Left cs | all null (map snd cs) -> m
                                                                              | otherwise             -> X.MGuarded (X.GLetTypes (Left cs)) m
                                                                      Right (args, results, f)        -> X.MGuarded (X.GLetTypes (Right (args, results, f))) m)
                                                      (X.MGuarded (X.GSubst evsubst) (payload rBody))
                                                      cbindss)
                        , assumed = assumedC ++ assumed rExpr ++ assumed rBody
                        , goals = goalsC ++ goals rExpr ++ rs
                        , used = used }

             where flattenArrows (TyApp (At _ (TyApp (At _ (TyVar _)) at)) (At _ rt))
                                      = let (args', result) = flattenArrows rt
                                        in (at : args', result)
                   flattenArrows t    = ([], t)

--                   existentialPredicates extVars determining deferred expected =
--                       do extVars <- concatMap tvs `fmap` mapM (substitute . TyVar) extVars
--                          expected' <- substitute expected
--                          determining' <- mapSndM substitute determining
--                          deferred' <- mapM (substitute . snd) deferred
--                          let vs              = tvs expected' ++ concatMap tvs deferred'
--                              escapingExtVars = filter (`elem` vs) extVars
--                          return (filter (\(id, p) -> any (`elem` escapingExtVars) (tvs p)) determining')

         PTyped p tys ->
             do v <- fresh "x"
                checkMatch (MGuarded (GFrom p (introduced (ELet (Decls [Explicit (v, [], MCommit e) (ForallK [] tys)])
                                                                (introduced (EVar v)))))
                                     m)
                           expected
         PGuarded p g ->
             checkMatch (MGuarded (GFrom (At l p) e) (MGuarded g m)) expected

----------------------------------------------------------------------------------------------------
--

checkFunction :: [Id] -> Match Pred KId -> Ty -> TcRes X.Expr
checkFunction params body expected =
    checkExpr (foldr elam (introduced (EMatch body)) params) expected
    where elam v e = introduced (ELam v e)

-- The Quill paper describes an improvement regime for Fun (->) predicates, as follows.  If a type
-- variable 'f' is constrained only by predicates of the form 'Fun f', then it's safe to improve it
-- to either the linear (-:>) or unrestricted (-!>) function types.  If it's also constrained by 'Un
-- f', then it's safe to improve it to the unrestricted (-!>) function type.
--
-- This is based on three things: the knowledge that there are only two possible ways to satisfy the
-- (->) constraint, that the linearity of both is defined, and that there is no other way to
-- distinguish the two types.  Some of the reasoning here should make its way into the Solver: for
-- example, that the constraints Un f, (->) f have only one possible solution.  However, the
-- knowledge that (->) f (without other constraints) can be improved is probably still not
-- generalizable.
--
-- This function implements that improvement.  The remaining complexity is to do with >:=
-- constraints.  If we hope to default a variable 'f', then constraints of the form 'T >:= f' pose
-- no difficulty.  On the other hand, constraints of the form 'f >:= T' do pose a problem: our
-- defaults are only valid if 'T' is linear.  For the moment, we address the case in which the 'T's
-- are other function types: as long as all the '>:=' constraints relate variables up for
-- defaulting, we're happy to default them all.

improveFunPredicates :: Preds -> Preds -> M Preds
improveFunPredicates assumed goals =
    traceIf (not (null goals)) (show ("Predicates for defaulting:" <+> pprList' ps)) $
    traceIf (not (null defaulted)) (show ("Defaulting:" <+> pprList defaulted)) $
    do modify (\st -> st{ currentSubstitution = defaults `composeU` currentSubstitution st })
       let goals' = filter (all (`notElem` defaulted) . tvs . snd) goals
       trace (show ("Remaining goals:" <+> pprList' (map snd goals')))
             (return goals')

    where ps = map snd (assumed ++ goals)

          funVar (At _ (Pred "->" [At _ (TyVar v)] Holds)) = Just v
          funVar _ = Nothing
          funVars = filter defaultable $ catMaybes (map funVar ps)

          defaultable v = all (funPred .||. gtePred) qs
              where funPred p = isJust (funVar p)
                    gtePred (At _ (Pred ">:=" _ Holds)) = True
                    gtePred _    = False
                    qs = filter ((v `elem`) . tvs) ps
                    (f .||. g) x = f x || g x

          orderings = [ends | p <- filter (any (`elem` funVars) . tvs) ps, ends <- endpoints p]
              where endpoints (At _ (Pred ">:=" [At _ t, At _ u] Holds)) = [ends t u]
                        where ends (TyApp (At _ (TyApp (At _ (TyVar v)) _)) _) (TyApp (At _ (TyApp (At _ (TyVar w)) _)) _) = (v, w)
                              ends (TyVar v) (TyApp (At _ (TyApp (At _ (TyVar w)) _)) _) = (v, w)
                              ends (TyApp (At _ (TyApp (At _ (TyVar v)) _)) _) (TyVar w) = (v, w)
                              ends (TyVar v) (TyVar w) = (v, w)
                    endpoints _ = []

          loop vs | vs == ws = vs
                  | otherwise = trace (show (pprList vs <+> "-->" <+> pprList ws)) $ loop ws
              where ws = filter (\v -> and [(v == w) ==> (w' `elem` vs) | (w, w') <- orderings]) vs
                    a ==> b = if a then b else True

          defaulted = loop funVars
          defaults = (K.empty, new [(v, linArrTy) | v <- defaulted])

checkTypingGroup :: TypingGroup Pred KId -> TcRes (X.Defns, TyEnv)

checkTypingGroup (Explicit (name, params, body) expectedTyS) =
    trace ("Inferring type for " ++ show (ppr name <::> ppr expectedTyS)) $
    do -- Instantiate declared type signatures
       (declaredKVars, declaredTyVars, declaredPredicates :=> At _ declaredType) <- instantiate expectedTyS
       evvars <- freshFor "e" declaredPredicates
       envvars <- freeEnvironmentVariables
       let declaredPreds  = zip evvars declaredPredicates
           transparents   = tvs declaredType ++ envvars

       -- Add error reporting once we know the instantiation of the expected signature; that way,
       -- type variables in the error will line up with the way we report the expected type.
       transformFailures (addErrorContext declaredKVars declaredTyVars declaredPredicates declaredType) $
           do trace (show ("Simplifying declared type" <+> ppr (declaredPredicates :=> introduced declaredType)))
                    (solve transparents (tvs declaredType) declaredPreds)   -- This is done for its side effect: computing improvement from the declared predicates.
              expected <- substitute declaredType

              (body', evsubst, assumed, goals, used) <-
                  withGeneric (declaredTyVars, declaredKVars) $
                      do -- Check that body has declared type
                         rBody <- contractRecursive introducedLocation name $ checkFunction params body expected -- (body', ps)
                         -- Simplify the inferred goals with respect to the assumptions
                         (evsubst, goals', cbindss) <-
                             traceIf (not (null (goals rBody))) "Discharging inferred from expected predicates" $
                                 entails transparents (tvs declaredType) (assumed rBody ++ declaredPreds) (goals rBody)
                         return (foldr (\cbinds e ->
                                            case cbinds of
                                              Left cs | all null (map snd cs) -> e
                                                      | otherwise             -> X.ELetTypes (Left cs) e
                                              Right (args, results, f)        -> X.ELetTypes (Right (args, results, f)) e)
                                       (payload rBody)
                                       cbindss,
                                 evsubst, assumed rBody, goals', used rBody)

              (retainedGoals, deferredGoals) <- splitPredicates goals
              retainedGoals' <- improveFunPredicates assumed retainedGoals
              (_, deferredAssumptions) <- splitPredicates assumed

              -- Check whether the specified assumptions were enough to prove the non-deferred
              -- goals.
              when (not (null retainedGoals')) $
                   do fds <- inducedDependencies (map snd (declaredPreds ++ goals))
                      transformFailures (addAmbiguousVariables (tvs (map snd retainedGoals') \\ close (tvs expected) fds) (map snd retainedGoals')) $
                          contextTooWeak assumed retainedGoals'

              return R{ payload = ([X.Defn name (convert expectedTyS)
                                                (Right (X.Gen declaredTyVars
                                                         evvars
                                                         (X.ESubst [] evsubst body')))],
                                   Map.singleton name (LetBound expectedTyS))
                      , assumed = deferredAssumptions
                      , goals = deferredGoals
                      , used = used }

    where addErrorContext kvs tvs ps t msg = iter tvs
              where iter (v:vs) = bindingTyVar v (const (iter vs))
                    iter []     = msg <$> indent 4 (hang 4 ("In the explicit binding for" <+>
                                                            ppr name <::> ppr (ForallK kvs (Forall tvs (ps :=> introduced t)))))

          -- In this code, we want to shorten type variables names, in parallel with the shortening
          -- that occurs in the wrapped error message.  However, the instance of Printable for
          -- variables can't shorten names---in particular, that instance doesn't know whether a
          -- variable is an expression, type, or evidence variable.  'tyvarName' is a lower-level
          -- IMPEG printer that provides type variable name shortening.
          addAmbiguousVariables avars ps msg =
              case nub avars of
                [] -> msg
                [v] -> msg <$> shorten ps (hang 4 ("Note: the type variable" <+> tyvarName v <+> "is ambiguous."))
                vs  -> msg <$> shorten ps (hang 4 ("Note: the type variables" <+> shorten ps (hsep (punctuate comma (map tyvarName vs))) <+> "are ambiguous."))

checkTypingGroup (Implicit fs) =
    appendFailureContext ("In the implicitly typed bindings for" <+> hsep (punctuate comma [ppr name | (name, _, _) <- fs])) $
    do -- Generate new type variables for functions
       ts <- replicateM (length fs) (newTyVar KStar)
       -- Check function bodies in environment with aforementioned type variables
       let env = Map.fromList (zip ids (map LamBound ts))
       eqnRs <- sequence [declare env (contractRecursive introducedLocation name (checkFunction ps body t)) | ((name, ps, body), t) <- zip fs ts]

       (assumedC, goalsC, used) <- contractMany introducedLocation (map used eqnRs)

       let fs'        = map payload eqnRs
           theGoals   = goalsC ++ concatMap goals eqnRs
           theAssumed = assumedC ++ concatMap assumed eqnRs

       -- Solve any solvable predicates; determine which of the remaining predicates can be deferred
       -- to the surrounding expression.

       envvars <- freeEnvironmentVariables
       let transparents = tvs ts ++ envvars

       (evsubst, theGoals', cbindss) <-
           traceIf (not (null theGoals))
                   (show ("Simplifying inferred predicates" <+> pprList' (map snd theGoals)))
                   (entails transparents (tvs ts) theAssumed theGoals)

       (_, deferredAssumptions) <- splitPredicates theAssumed
       (retained, deferred) <- splitPredicates theGoals'

       -- Compute type signatures for the implicit declarations, and check whether or not they're
       -- ambiguous.  For the ambiguity check, we'll need to know the functional dependencies for
       -- the retained predicates.

       -- The ambiguity check is different than that in Haskell: our ambiguity check extends to
       -- quantification in addition to qualification.  The following example is legal in Haskell:
       --
       --   f xs = null xs || g True
       --   g y  = y || f []
       --
       -- However, it is not legal in Habit, as there is no way to determine the type argument to f
       -- from the call in g.  This could be resolved with a suitable clever defaulting mechanism:
       -- for example, GHC inserts a dummy "Any" type when compiling these functions.  It is not
       -- clear that such a defaulting mechanism would be appropriate in Habit; in particular, we
       -- imagine that there might be choices of representation that would be effected by the choice
       -- of default type.

       ts' <- mapM substitute ts
       let ts = foldr1 intersect (map tvs ts')
           (ambiguous, unambiguous) = partition (any (`notElem` ts) . tvs . snd) retained

       ambiguous' <- improveFunPredicates theAssumed ambiguous
       let (retainedVs, retainedPs) = unzip (ambiguous' ++ unambiguous)
       qs <- mapM (substitute . snd) theGoals'
       ts'' <- mapM substitute ts'
       fds <- inducedDependencies qs
       let rvs = nub (tvs retainedPs)
           quantifyingVs = nub (rvs ++ tvs ts'') \\ envvars -- hyper-efficient
           -- 'qualify t' begins by computing the determined variables given the type t and the
           -- functional dependencies from retained.  If all the variables in retained are
           -- determined, it generates a type scheme by quantifying over all the variables in
           -- 'retained => t'; otherwise, it complains about ambiguous types.  Again, we've lost the
           -- information to give a good error location here.
           qualify t =
               let determined = close (tvs t ++ envvars) fds
                   qty = retainedPs :=> introduced t
                   ambiguities = filter (`notElem` determined) quantifyingVs
               in case ambiguities of
                    [] -> return (quantify quantifyingVs qty)
                    vs -> failWith (ambiguousTypeError vs qty)

       tyss <- trace (show (hang 4 ("From predicates" <+> cat (punctuate ", " (map ppr qs)) <$>
                                   "induced dependencies" <+> cat (punctuate ", " (map ppr fds))))) $
               mapM qualify ts''

       let functions    = [X.Defn id (convert tys)
                                     (Right (X.Gen quantifyingVs
                                                   retainedVs
                                                   (foldr (\cbinds e ->
                                                               case cbinds of
                                                                 Left cs | all null (map snd cs) -> e
                                                                         | otherwise             -> X.ELetTypes (Left cs) e
                                                                 Right (args, results, f)        -> X.ELetTypes (Right (args, results, f)) e)
                                                          (X.ESubst replacements evsubst f)
                                                          cbindss)))
                          | (id, tys, f) <- zip3 ids tyss fs']
           replacements = [(id, X.ELetVar (X.Inst id (map X.TyVar quantifyingVs) (map X.EvVar retainedVs)))
                          | id <- ids]

       trace (show (hang 4 ("Inferred types" <$>
                            vcat [ppr id <::> ppr tys <+> "(generalized from" <+> ppr t <> ")" | (id, tys, t) <- zip3 ids tyss ts']) <$>
                    "With free environment variables" <+> cat (punctuate (comma <> space) (map ppr envvars))))
             (return R{ payload = (functions, Map.fromList (zip ids (map LetBound tyss)))
                      , assumed = deferredAssumptions
                      , goals = deferred
                      , used = used })

    where ids = [name | (name, _, _) <- fs]
          ambiguousTypeError avs qty = shorten qty message
              where message
                        | length avs == 1 = "Ambiguous type variable" <+> ppr (head avs) </> "in type" <+> ppr qty
                        | otherwise       = "Ambiguous type variables" <+> hsep (punctuate comma (map ppr avs)) <$> "in type" <+> ppr qty

-- Suppose we have a (Surface) typing group of the form
--
--   x1 :: T1
--   x3 :: T3
--   K x1 _ x3 = m
--
-- To check this group, we rewrite it to the following (MPEG) group of bindings:
--
--   v = let rhs = m => p[yi/xi] <- rhs => (x1, x3)
--   x1 :: T1
--   x1 = p2_0 v
--   x2 :: T2
--   x2 = p2_1 v
--
-- This causes problems from a linearity perspective: in the original definition, the components of
-- 'm' are used linearly, while in the rewritten version they are not.  I see two possible
-- resolutions.  The first is to introduce some form of primitive pattern matching---say, for
-- tuples.  Then, instead of the rewriting above, we would rewrite to
--
--   (x1, x2) = let rhs = m => p[yi/xi] <- lhs => let xi :: Ti; xi = yi => (x1, x2)
--
-- which preserves the linearity.  I think this might actually be the preferable option---I can
-- imagine advantages to preserving tuples through the back-end.  However, it also requires more
-- extensive changes.  So, for the time being, I'm cheating, by avoiding the contraction check on
-- the xi bindings.

checkTypingGroup (Pattern (At l p) m signatures) =
    appendFailureContext ("In the pattern bindings for" <+> hsep (punctuate comma (map ppr (bound p)))) $
    do tupleVar <- fresh "v"
       rhsVar   <- fresh "rhs"
       vs'      <- mapM fresh vs
       let body       = MGuarded (GLet (Decls [Implicit [(rhsVar, [], m)]]))
                                 (MGuarded (GFrom (At l (rename (zip vs vs') p)) (At l (EVar rhsVar)))
                                           (MCommit (introduced (foldl eapp (ECon (fromString ("$Tuple" ++ show (length vs)))) (map EVar vs')))))
           components = [makeTypingGroup (v, [], MCommit (At l (eapp (EVar (fromString ("$t" ++ show n ++ '_' : show m))) (EVar tupleVar)))) | (v,m) <- zip vs [0..]]
       rBody <- checkTypingGroup (Implicit [(tupleVar, [], body)])
       let (tupleGroup, tupleEnv) = payload rBody
       componentRs <- mapM (binds l tupleEnv . checkTypingGroup) components
       let (componentGroups, componentEnvs) = unzip (map payload componentRs)
       return R{ payload = (concat (tupleGroup : componentGroups), Map.unions (tupleEnv : componentEnvs))
               , assumed = assumed rBody ++ concatMap assumed componentRs
               , goals = goals rBody ++ concatMap goals componentRs
               , used = used rBody } -- Cheat: I'm not checking the 'used' bits of the component results.
    where vs        = bound p
          n         = length vs
          eapp e e' = EApp (introduced e) (introduced e')

          lookupSignature id [] = Nothing
          lookupSignature id (Signature id' tys : rest)
              | id == id'       = Just tys
              | otherwise       = lookupSignature id rest

          makeTypingGroup f@(id, _, _) =
              case lookupSignature id signatures of
                Nothing -> Implicit [f]
                Just tys -> Explicit f tys

checkTypingGroup (PrimValue (Signature name expectedTyS) str) =
    return R{ payload = ([X.Defn name (convert expectedTyS) (Left (str, []))],
                         Map.singleton name (LetBound expectedTyS))
            , assumed = []
            , goals = []
            , used = [] }

----------------------------------------------------------------------------------------------------

checkDecls :: Decls Pred KId -> TcRes (X.Decls, TyEnv)
checkDecls (Decls groups) =
    do rg <- declare (Map.fromList (signatures groups)) (checkGroups groups)
       let (groups', vals) = payload rg
       return rg{ payload = (X.Decls (concat groups'), vals) }
    where checkGroups [] = return R{ payload = ([], Map.empty)
                                   , assumed = []
                                   , goals = []
                                   , used = [] }
          checkGroups (g:gs) =
              do rg <- checkTypingGroup g
                 let (g', vals) = payload rg
                 rgs <- declare vals (checkGroups gs)
                 let (gs', vals') = payload rgs
                 (assumedC, goalsC, used) <- contract introducedLocation (used rg) (used rgs)
                 return R{ payload = (g' : gs', Map.union vals' vals)
                         , assumed = assumedC ++ assumed rg ++ assumed rgs
                         , goals = goalsC ++ goals rg ++ goals rgs
                         , used = used }

          -- flatten typing groups

          signatures []                                 = []
          signatures (Explicit (name, _, _) tys : rest) = (name, LetBound tys) : signatures rest
          signatures (Implicit _ : rest)                = signatures rest
          signatures (Pattern _ _ ss : rest)            = [(name, LetBound tys) | Signature name tys <- ss] ++ signatures rest
          signatures (PrimValue (Signature name tys) _ : rest) = (name, LetBound tys) : signatures rest
