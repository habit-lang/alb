{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Solver.Validation where

import Control.Arrow (first)
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Either
import Data.List
import Data.Maybe

import Solver.PP
import Solver.Main (remaining, solve, solveAnonymous, Answer(..), Query(..))
import Solver.Oracles (primitiveClasses)
import Solver.Subst
import Solver.Syntax
import Solver.Trace
import qualified Syntax.IMPEG.KSubst as K

----------------------------------------------------------------------------------------------------
-- Utilities

isRight :: Either t u -> Bool
isRight (Left _) = False
isRight _        = True

subset xs ys = all (`elem` ys) xs
same xs ys = xs `subset` ys && ys `subset` xs

pairs _ []      = []
pairs xs (y:ys) = (y, xs ++ ys) : pairs (y:xs) ys

----------------------------------------------------------------------------------------------------
-- Validation monad

newtype V t = V { unV :: StateT Int (WriterT [String] (Either String)) t }
    deriving (Functor, Applicative, Monad, MonadState Int, MonadError String, MonadWriter [String])

runV :: V t -> Either String (t, [String])
runV c = runWriterT (evalStateT (unV c) 0)

runV_ :: V t -> (t, [String])
runV_ c = case runV c of
            Left err -> error ("runV_: failed: " ++ err)
            Right x -> x

runSolver :: (Int -> (Answer, Int)) -> V Answer
runSolver f = (fst . f) `fmap` get

fresh :: Id -> V Id
fresh (Ident s _ f) = do n <- get
                         put (n + 1)
                         return (Ident s n f)

conditional :: (V t) -> (t -> V u) -> V u -> V u
conditional cond cons alt =
    (cond >>= cons) `catchError` const alt

unify' :: Unifies x => x -> x -> V Subst
unify' x y = case unify ([], []) x y of
               Left err -> throwError err
               Right s  -> return s

match' :: Unifies x => x -> x -> V Subst
match' x y = case match ([], []) x y of
               Left err -> throwError err
               Right s  -> return s

unifies :: Unifies x => x -> x -> Bool
unifies x y = either (const False) (const True) (runV (unify' x y))

instantiate :: HasVars x => x -> V x
instantiate x =
    do vs' <- mapM freshM vs
       let s = S K.empty [v :-> v' | (i, v, v') <- zip3 [0..] vs vs']
       return (s ## x)
    where vs = vars x
          freshM (Kinded v k) =
              do v' <- fresh v
                 return (TyVar (Kinded v' k))

instantiateScheme :: HasVars x => Scheme x -> V ([Type], x)
instantiateScheme (Forall ks x) =
    do vs <- replicateM (length ks) (fresh "t")
       let ts = [TyVar (Kinded v k) | (v, k) <- zip vs ks]
       return (ts, inst ts x)

instantiateAxiom :: Axiom -> V (Name, [QPred])
instantiateAxiom (Ax name rules) =
    do rules' <- mapM instantiateScheme rules
       return (name, map snd rules')

warn :: String -> V ()
warn s = tell [s]

checkInconsistent :: FunDeps -> Pred -> [Pred] -> Bool
checkInconsistent fundeps p ps = any (`unifies` invert p) ps || any fdInconsistent ps
    where classFDs = fromMaybe [] (lookup cl fundeps)
              where Pred cl _ _ _ = p
          fdInconsistent p' = or [fdeq f p p' && not (unifies p p') | f <- classFDs]
              where fdeq f = modFD (==) f

----------------------------------------------------------------------------------------------------
-- Validation results
--
-- This type is remarkably similar to Maybe; however, the usage is backwards from the usual meaning
-- of the Maybe type.

data ValidationResult t = Ok | Fail t

firstFailure :: [ValidationResult t] -> ValidationResult t
firstFailure []           = Ok
firstFailure (Ok : rest)  = firstFailure rest
firstFailure (Fail x : _) = Fail x

instance Functor ValidationResult
    where fmap f Ok = Ok
          fmap f (Fail t) = Fail (f t)

----------------------------------------------------------------------------------------------------
-- Functional Dependencies

-- Given a set of funtional dependencies, a set of predicates (the context), and a set of determined
-- varaibles, this function finds all the variables that are determined by the functional
-- dependencies that apply to the context.  For example:
--   closeDetermined [F t u | t ~> u] [F a b, F b c] [a] == [b, c]
-- (The function actually uses variable names instead of variables, since tyvars are not a distinct
-- type in the AST.)
closeDetermined :: FunDeps -> [Pred] -> [TyId] -> [TyId]
closeDetermined fds context determined = loop determined
    where loop determined | same determined expanded = determined
                          | otherwise                = loop expanded
              where expanded = nub (determined ++ concatMap (expandByPred determined) context)

          expandByPred soFar (Pred cl ts _ _) = concatMap expandFD classFDs
              where classFDs = fromMaybe [] (lookup cl fds)
                    expandFD (determining :~> determined)
                        | all (isDetermined soFar) (map (ts !!) determining) = vars (map (ts !!) determined)
                        | otherwise                                          = []
                    isDetermined ds t = vars t `subset` ds

covering :: FunDeps -> QPred -> ValidationResult (Id, [FunDep])
covering fds (context :=> Pred cl ts Exc _) = Ok
covering fds (context :=> Pred cl ts Inc _) = firstFailure (map check classFDs)
    where classFDs = fromMaybe [] (lookup cl fds)
          check fd@(determining :~> determined)
              | vars (map (ts !!) determined) `subset` allDetermined = Ok
              | otherwise                                            = Fail (cl, [fd])
              where allDetermined = closeDetermined fds context (vars (map (ts !!) determining))

mergeFDs :: FunDeps -> FunDeps -> FunDeps
mergeFDs [] fds = fds
mergeFDs all@((name, fds):rest) oldFDs =
    traceInput (ppx (name, fds) ++ ".") $
    case partition ((name ==) . fst) oldFDs of
      ([], oldFDs) -> mergeFDs rest ((name, fds) : oldFDs)
      ([(_, fds')], oldFDs) -> mergeFDs rest ((name, fds ++ fds') : oldFDs)
      _ -> error "mergeFDs"

----------------------------------------------------------------------------------------------------
-- Overlapping instances

overlapping :: Axioms -> FunDeps -> Requirements -> Opacities -> QPred -> QPred -> V (ValidationResult Subst)
overlapping axioms fds rqs ops (qs :=> p@(Pred clName ts _ _)) qp =
    firstFailure `fmap` mapM overlappingAt classFDs

    where classFDs = ([0..length ts - 1] :~> []) : fromMaybe [] (lookup clName fds)

          overlappingAt :: FunDep -> V (ValidationResult Subst)
          overlappingAt fd =
              do qs' :=> p' <- if flag p == flag qp
                               then instantiate qp
                               else instantiate (invert qp)

                 overlapping <- conditional ((unify' `modFD` fd) p p')
                                            (\s -> case compressPredicates (s ## (qs ++ qs')) of
                                                     Nothing -> return Ok
                                                     Just ps -> trace ("Checking coherence of (" ++ ppx (s ## qs :=> p) ++ ") and (" ++ ppx (s ## (qs' :=> p'))) $
                                                                do b <- forwardConsistent (length ps) ps
                                                                   b' <- disproves [] ps
                                                                   return (if not b || b' then Ok else Fail s))
                                            (return Ok)

                 inconsistent <- conditional ((unify' `atDetermining` fd) p p')
                                             (\s -> if ((==) `atDetermined` fd) p p'
                                                    then return Ok
                                                    else let sqs :=> sp     = s ## (qs :=> p)
                                                             sqs' :=> sp'   = s ## (qs' :=> p')
                                                             vs             = (vars `atDetermining` fd) (s ## p)
                                                             ws             = closeDetermined fds (sqs ++ sqs') vs
                                                             constrains vs p = null vs' || any (`elem` vs) vs'
                                                                 where vs'  = vars p
                                                             determining    = filter (constrains vs) (sqs ++ sqs')
                                                             determined     = filter (constrains ws) sqs
                                                             determined'    = filter (constrains ws) sqs'
                                                         in trace (unlines ["Checking consistency of (" ++ ppx (s ## (qs :=> p)) ++ ") and (" ++ ppx (s ## (qs' :=> p')) ++ ") under " ++ ppx (clName, [fd]),
                                                                            "   determining predicates are " ++ intercalate ", " (map ppx determining),
                                                                            "   and determined predicates are " ++ intercalate ", " (map ppx determined) ++ " and " ++ intercalate ", " (map ppx determined')]) $
                                                            case compressPredicates determining of
                                                              Nothing -> return Ok
                                                              Just determining' ->
                                                                  do consistent <- forwardConsistent (length determining') determining'
                                                                     leftDisprovesRight <- disproves (determining' ++ determined) determined'
                                                                     rightDisprovesLeft <- disproves (determining' ++ determined') determined
                                                                     return (trace ("Results are: " ++ intercalate " " (map show [not consistent, leftDisprovesRight, rightDisprovesLeft])) $
                                                                             if not consistent || (leftDisprovesRight && rightDisprovesLeft)
                                                                             then Ok
                                                                             else Fail s))
                                             (return Ok)

                 return (firstFailure [overlapping, inconsistent])

              where compressPredicates = foldM compress []
                        where compress ps p
                                  | checkInconsistent fds p ps = Nothing
                                  | any (`contains` p) ps      = Just ps
                                  | otherwise                  = Just (p : ps)

                    forwardConsistent n facts
                        | length facts > 5 * n =
                            return True
                        | otherwise =
                            trace (ppx facts) $
                            do facts' <- concatMapM (expand facts) axioms
                               case compressPredicates (facts ++ facts') of
                                 Nothing      -> return False
                                 Just facts'' -> if same facts facts''
                                                 then return True
                                                 else forwardConsistent n facts''

                    expand :: [Pred] -> Axiom -> V [Pred]
                    expand facts ax =
                        do (_, qs) <- instantiateAxiom ax
                           expand' qs facts

                    expand' :: [QPred] -> [Pred] -> V [Pred]
                    expand' [] facts = return []
                    expand' (clause:clauses) facts =
                        liftM2 (++)
                               (expandMatch clause facts)
                               (expandSkip clause clauses facts)

                    expandMatch :: QPred -> [Pred] -> V [Pred]
                    expandMatch ([] :=> p) _ = return [p]
                    expandMatch ((q : qs) :=> p) facts =
                        concatMapM (\f -> conditional (f `match'` q) (\s -> expandMatch ((s ## qs) :=> (s ## p)) facts) (return []))
                                   facts

                    expandSkip :: QPred -> [QPred] -> [Pred] -> V [Pred]
                    expandSkip (qs :=> _) qps facts =
                        concat `fmap` (sequence [ conditional (f `match'` invert q) (\s -> expand' (s ## qps) facts) (return [])
                                                      | f <- facts, q <- qs ])

                    disproves ps qs =
                        do result <- runSolver (solveAnonymous (Q axioms fds rqs ops ([], []) [] [] ps qs))
                           case result of
                             AnsFailed {} -> return True
                             _            -> return False

----------------------------------------------------------------------------------------------------
-- Requirements

mergeRequirements :: FunDeps -> Requirements -> Requirements -> V ([String], Requirements)
mergeRequirements fds oldRqs newRqs =
    traceInput (intercalate "\n" (map ppxInstantiated newRqs)) $
    do (failures, successes) <- partitionEithers `fmap` mapM (checkRequirement oldRqs) newRqs
       return (failures, successes ++ oldRqs)
    where ppxInstantiated (Forall ks rq) = pp 0 (inst [TyVar (Kinded (fromString c) KStar) | c <- names] rq) ++ "."

          checkRequirement oldRqs rqScheme =
              return (Right rqScheme) {-

              do (_, rq@(Requires ps _)) <- instantiateScheme rqScheme
                 closed <- expand ps (rqScheme:oldRqs)
                 case closed of
                   Just ps | all (\p -> not (checkInconsistent fds p ps)) ps ->
                       return (Right rqScheme)
                   _ ->
                       return (Left ("The requirement " ++ ppx rq ++ " is inconsistent.\n"))

              where expand [] _ = return (Just [])
                    expand ps rqs =
                        do ps' <- concatMapM (expandBy ps) rqs
                           mps <- contract (ps ++ ps')
                           case mps of
                             Nothing                  -> return Nothing
                             Just ps'' | same ps ps'' -> return (Just ps)
                                       | otherwise    -> expand ps'' rqs

                    expandBy ps rqsc =
                        do (_, Requires qs qs') <- instantiateScheme rqsc
                           ss <- multimatch ps qs
                           return (concatMap (## (map snd qs')) ss)

                        where multimatch _ [] = return [empty]
                              multimatch ps (q:qs) =
                                  concat `fmap` sequence [ conditional (match' p q)
                                                                       (\s -> do ss <- multimatch (s ## ps') (s ## qs)
                                                                                 return [s' `compose` s | s' <- ss])
                                                                       (return [])
                                                           | (p, ps') <- pairs [] ps ]

                    contract :: [Pred] -> V (Maybe [Pred])
                    contract ps = do substs <- sequence [pairwiseImprovements p q | (p:qs) <- tails ps, q <- qs]
                                     return (do ss <- sequence (concat substs)
                                                s  <- combine ss
                                                return (nub (s ## ps)))
                        where combine ss =
                                  foldr (\s ms -> ms >>= (\s' -> if consistent s s' then return (compose s s') else Nothing))
                                        (Just empty) ss
                              pairwiseImprovements p@(Pred cl _ Inc _) q@(Pred cl' _ Inc _)
                                  | cl /= cl' = return []
                                  | otherwise = mapM try classFDs
                                  where classFDs = fromMaybe [] (lookup cl fds)
                                        try fd = conditional ((unify' `atDetermining` fd) p q)
                                                             (\s -> conditional ((unify' `atDetermined` fd) (s ## p) (s ## q))
                                                                                (return . Just)
                                                                                (return Nothing))
                                                             (return (Just empty))
                              pairwiseImprovements _ _ = return [] -}


-- Formally, a requirement P => Q is satisfied in a program if in all models of the program,
-- whenever a ground instance of the hypotheses P are modelled, the corresponding ground instance of
-- the conclusions Q is modelled.  For implementation purposes, this means that if there is given
-- axioms clauses pi_i <= P_i such that the pi_i's match the hypotheses P, we must have that Q is
-- provable from the union of the P_i's.
--
-- TODO: this implementation treats each clause of an axiom separately, ignoring the sequencing of
-- instance chains.
--
-- In the implementation, we verify instances as they are encountered, instead of verifying the
-- program as a whole.  This means that we can fix one of the axioms, and only need to consider all
-- available solutions to the others.

satisfies :: Axioms -> FunDeps -> Requirements -> Opacities -> Axiom -> (Scheme Requirement, Requirement) -> V (Maybe RqImpls)
satisfies _ _ _ _ (Ax _ []) _ = return (Just (RqImpls []))
satisfies axs fds rqs ops ax@(Ax name clauses) (rqsc, Requires ps qs) =
    do rqimpls <- mapM (clauseSatisfies ps qs) (zip clauseNames clauses)
       return (combine `fmap` sequence rqimpls)
    where clauseNames | null (tail clauses) = [AxId (nameFrom name) Nothing]
                      | otherwise           = [AxId (nameFrom name) (Just i) | i <- [0..]]

          clauseSatisfies ps qs (axid, qpsc) =
              trace ("clauseSatisfies: " ++ ppx ps ++ ", " ++ ppx qs ++ ", " ++ ppx qpsc) $
              do (ts, ps' :=> p') <- instantiateScheme qpsc
                 let names = [fromString ("g" ++ show i) | i <- [1..length ps']]
                 rqimpls <- sequence [ conditional (match' p' r)
                                                   (\s -> enumerate (zip names ps') (s ## (map snd rs)) (s ## qs)
                                                                    (i, Pat axid (s ## ts) names) [] (length ps' + 1))
                                                   (return (Just (RqImpls [])))
                                       | ((i, r), rs) <- pairs [] (zip [0..] ps) ]
                 return (combine `fmap` sequence rqimpls)

          enumerate ps' [] qs (i,pt) prpats _ =
              trace ("enumerate: " ++ intercalate ", " [ppx ps', ppx prpats, ppx qs]) $
              isProven `fmap` runSolver (solve (Q (ax:axs) fds (rqsc:rqs) ops ([], []) [] [] ps' qs))
              where isProven (AnsProved proofs _ _ _) = let impls = RqImpls [(rid, [(insert i pt (reverse prpats), pr)]) | (rid, pr) <- proofs]
                                                        in trace ("satifies: " ++ ppx impls) (Just impls)
                    isProven _                      = Nothing
                    insert 0 x ys     = x : ys
                    insert n x (y:ys) = y : insert (n - 1) x ys

          enumerate ps' (r@(Pred cl _ _ _):rs) qs ipt prpats z
              | cl `elem` primitiveClasses = enumerate ((fromString ("g" ++ show z), r):ps') rs qs ipt (Wild : prpats) (z + 1)
              | otherwise = trace ("enumerate: " ++ intercalate ", " [ppx ps', ppx (r:rs), ppx qs, ppx prpats]) $
                            do clauses <- concatMapM instantiateAxiom' (ax:axs)
                               rqimpls <- sequence [ conditional (unify' r p)
                                                                 (\s -> let vs = [fromString ("g" ++ show i) | i <- [z..]]
                                                                        in enumerate (s ## (zip vs ps ++ ps')) (s ## rs) (s ## qs)
                                                                                     (s ## ipt) (Pat axid (s ## ts) (take (length ps) vs) : (s ## prpats)) (z + length ps))
                                                                 (return (Just (RqImpls [])))
                                                     | (axid, ts, ps :=> p) <- clauses ]
                               return (combine `fmap` sequence rqimpls)
              where instantiateAxiom' (Ax name clauses) =
                        do clauses' <- mapM instantiateScheme clauses
                           case clauses' of
                             [(ts, qp)] -> return [(AxId (nameFrom name) Nothing, ts, qp)]
                             _  -> return [(AxId (nameFrom name) (Just i), ts, qp) | (i, (ts, qp)) <- zip [0..] clauses']

combine :: [RqImpls] -> RqImpls
combine [] = RqImpls []
combine (rqimpls:rest) = RqImpls (foldr pairwise (un rqimpls) rest)
    where un (RqImpls is) = is
          pairwise rqimpls = foldr insert (un rqimpls)
          insert (rid, impls) [] = [(rid, impls)]
          insert (rid, impls) ((rid', impls'):rest)
              | rid == rid'      = (rid, impls ++ impls') : rest
              | otherwise        = (rid', impls') : insert (rid, impls) rest

----------------------------------------------------------------------------------------------------
-- Opacities

mergeOpacities :: Opacities -> Opacities -> Opacities
mergeOpacities [] ops = ops
mergeOpacities all@((name, ops):rest) oldOps =
    traceInput (ppx all) $
    case partition ((name ==) . fst) oldOps of
      ([], oldOps)          -> mergeOpacities rest ((name, ops) : oldOps)
      ([(_, ops')], oldOps) -> mergeOpacities rest ((name, ops ++ ops') : oldOps)
      _                     -> error "mergeOpacities"

----------------------------------------------------------------------------------------------------
-- Building axiom sets

addAxioms :: Axioms -> FunDeps -> Requirements -> Opacities -> [(Axiom, Bool)] -> V (Axioms, Axioms, RqImpls)
addAxioms axs fds rqs ops newAxioms =
    traceInput (unlines [ppxInstantiated ax ++ (if gfp then "!" else ".") | (ax, gfp) <- newAxioms]) $
    do newAxioms' <- simplifyLoop 0 newAxioms
       newInstAxioms <- (zip newAxioms' . map snd) `fmap` mapM instantiateAxiom newAxioms'
       oldInstAxioms <- (zip axs . map snd) `fmap` mapM instantiateAxiom axs
       sequence_ [checkOverlapping ax rest | (ax:rest) <- map ((++ oldInstAxioms)) (tail (reverse (tails newInstAxioms)))]
       mapM_ checkCovering newInstAxioms
       rqps <- zip rqs `fmap` mapM ((snd `fmap`) . instantiateScheme) rqs
       rqimplss <- sequence [checkRequirements rqps ax (axs' ++ axs) | (ax, axs') <- pairs [] newAxioms']
       return (newAxioms', newAxioms' ++ axs, combine rqimplss)

    where newAxiomPairs = [(axp, map fst axs) | (axp : axs) <- tails (gfps ++ lfps)]
              where (gfps, lfps) = partition snd newAxioms

          simplifyLoop :: Integer -> [(Axiom, Bool)] -> V Axioms
          simplifyLoop n axs = do (axs', progress) <- mapAccumM simplifyAxiom [] ps
                                  if or progress
                                  then trace ("Simplification loop: made progress, recurring:\n" ++ intercalate "\n" (map (("    " ++ ) . ppx . fst) axs')) $
                                       check checkSimplificationIterations (< n)
                                             ("Maximum simplification iterations exceeded.\n" ++ intercalate "\n" (map (("     " ++) . ppx . fst) axs')) $
                                       simplifyLoop (n + 1) axs'
                                  else trace ("Simplification loop: no progress, exiting:\n" ++ intercalate "\n" (map (("    " ++ ) . ppx . fst) axs')) $
                                       return (map fst axs')
              where ps = pairs [] axs
                    mapAccumM f z [] = return (z, [])
                    mapAccumM f z (x:xs) = do (z', y) <- f z x
                                              (z'', ys) <- mapAccumM f z' xs
                                              return (z'', y : ys)

          simplifyAxiom :: [(Axiom, Bool)] -> ((Axiom, Bool), [(Axiom, Bool)]) -> V ([(Axiom, Bool)], Bool)
          simplifyAxiom simplified ((Ax name clauses, gfp), remaining) =
              do (clauses', progress) <- unzip `fmap` mapM (simplifyClause axs' gfp) clauses
                 return ((Ax name clauses', gfp) : simplified, or progress)
              where axs' = map fst (simplified ++ remaining) ++ axs

          simplifyClause :: Axioms -> Bool -> Scheme QPred -> V (Scheme QPred, Bool)
          simplifyClause _   _   qps@(Forall _ ([] :=> _)) = return (qps, False)
          simplifyClause axs gfp qps@(Forall ks qp) =
              trace ("Simplifying clause " ++ ppx qps) $
              do result <- runSolver (solveAnonymous q)
                 case result of
                   AnsProved _ impr _ _ -> let newQPS | gfp = requantify [] (impr ## c)
                                                      | otherwise = requantify (impr ## hs) (impr ## c)
                                           in trace ("Simplified to " ++ ppx newQPS) (return (newQPS, not (clausesEqual qps newQPS)))
                   AnsStuck _ remaining impr _ ->
                       let remaining' = impr ## map snd remaining
                           c' = impr ## c
                           newQPS | gfp       = requantify remaining' c'
                                  | otherwise = requantify (impr ## hs) c'
                       in trace ("Simplified to " ++ ppx newQPS) (return (newQPS, not (clausesEqual qps newQPS)))
                   AnsFailed {} -> do warn ("Clause makes inconsistent assumptions: " ++ ppx qps)
                                      return (qps, False)

              where tyids = zipWith Kinded [fromString ("_t" ++ show i) | i <- [0..]] ks
                    (hs :=> c) = inst (map TyVar tyids) qp
                    q = Q { qAxioms = axs
                          , qFundeps = fds
                          , qRequirements = rqs
                          , qOpacities = ops
                          , qGenerics = ([], [])
                          , qUniformVariables = (vars hs ++ vars c)
                          , qTransparents = []
                          , qHypotheses = if gfp then [c] else []
                          , qGoals = hs }

                    requantify hs c = Forall (map kind vs) (gen 0 vs (hs :=> c))
                        where vs = nub (vars hs ++ vars c)

                    clausesEqual (Forall ks (ps :=> p)) (Forall ks' (qs :=> q)) =
                        ks == ks' && p == q && all (`elem`  qs) ps && all (`elem` ps) qs

          flattenValidationResult Ok = return ()
          flattenValidationResult (Fail s) = throwError s

          checkOverlapping :: (Axiom, [QPred]) -> [(Axiom, [QPred])] -> V ()
          checkOverlapping (axiom, qs) axs =
              flattenValidationResult =<< (firstFailure `fmap` mapM (overlaps qs) axs)
              where qs `overlaps` (ax, qs') =
                        do results <- sequence [overlapping (map fst axs) fds rqs ops qp qp' | qp <- qs, qp' <- qs']
                           return (failureString ax `fmap` firstFailure results)
                    failureString ax s = unlines ["Overlapping instances: " ++ ppx axiom, "overlaps with " ++ ppx ax]

          checkCovering (axiom, qs) =
              flattenValidationResult (failureString `fmap` firstFailure (map (covering fds) qs))
              where failureString fd = unlines ["The axiom " ++ ppx axiom, "violates the covering condition of " ++ ppx fd]

          checkRequirements rqps axiom axs =
              do results <- mapM (\(rq, others) ->
                                      do mrqimpls <- satisfies axs fds (map fst others) ops axiom rq
                                         case mrqimpls of
                                           Nothing      -> return (Left rq)
                                           Just rqimpls -> return (Right rqimpls))
                                  (pairs [] rqps)
                 case partitionEithers results of
                   ([], rqimplss) -> return (combine rqimplss)
                   ([rq], _)      -> throwError (unlines ["The axiom " ++ ppx axiom, "does not meet the requirement " ++ ppx (fst rq)])
                   (rqs, _)       -> throwError (unlines (("The axiom " ++ ppx axiom) :
                                                          "does not meet the requirements: " : map (ppx . fst) rqs))


          ppxInstantiated (Ax name qpschemes) =
              f (ppx name) ++
                  intercalate "; " [pp 0 (inst [TyVar (Kinded (fromString c) KStar) | c <- names] qp)
                                    | Forall _ qp <- qpschemes]
              where f "" = ""
                    f s = s ++ ": "
