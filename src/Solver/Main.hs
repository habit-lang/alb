{-# LANGUAGE FlexibleContexts, FlexibleInstances, PatternGuards, OverloadedStrings #-}
module Solver.Main where

import Control.Monad (liftM2, replicateM)
import Control.Monad.State
import Data.Char (ord, chr)
import Data.Either (partitionEithers)
import qualified Data.IntSet as Set
import Data.List
import Data.Maybe
import Data.Monoid(Monoid(..))
import Solver.Oracles
import Solver.PP
import Solver.Subst
import Solver.Syntax
import Solver.Tactics hiding (improvement, remaining)
import Solver.Trace

(f .||. g) x = f x || g x

----------------------------------------------------------------------------------------------------
-- Assumptions

assumeGoal :: Axioms -> FunDeps -> Opacities -> Tactic ()
assumeGoal axioms fds ops = node assume'
    where assume' (Goal name goal isRoot Nothing) =
              do assume axioms fds ops (\pid -> PAssump pid name) goal isRoot
                 try applySubst
          assume' _ =
              noProgress

          applySubst = node apply'
              where apply' (Goal name goal isRoot Nothing) = trail (applyAt name goal isRoot)
                    apply' _                               = noProgress

                    applyAt name goal isRoot tr
                        | goal == goal' = noProgress
                        | otherwise     = trace ("Improving " ++ ppx goal ++ " to " ++ ppx goal')
                                                (update (Goal name goal' isRoot Nothing))

                        where s = substitution tr
                              goal' = s ## goal

-- Adds an assumption, and its logical consequences (arising from requirements or functional
-- dependencies) to the trail.
assume :: Axioms -> FunDeps -> Opacities -> PCon -> Pred -> Bool -> Tactic ()
assume axioms fds ops pr p@(Pred cl _ _ _) isRoot = state assume' >>= fromRequirements
    where assume' st
              | any (\(_, _, p') -> sp == s ## p') (assumptions (_trail st)) =
                  trace ("Attemped to assume " ++ ppx p ++ " by " ++ ppx pr ++ ", but we already know that.") noProgress
              | otherwise =
                  do impr <- improvementFromAxioms axioms fds ops p
                     when (not (isEmpty impr))
                          (trace ("Computed improvement from assumption " ++ ppx p) (bind impr >> return ()))
                     addToTrail p pr
              where s = substitution (_trail st)
                    sp = s ## p

          fromRequirements i =
              do (newRqs, newAssumptions) <- partitionEithers `fmap`
                                             (mapM (\rq -> applyRequirement ops pr p rq `orElse` return (Left [])) =<<
                                              requirements)
                 require (Just i) (concat newRqs)
                 let newAssumptions' = concat newAssumptions
                 when isRoot $
                      let determined = concatMap (determinedFrom . snd) newAssumptions'
                          determinedFrom p@(Pred cl _ _ _) = concat [vars (p `atDetermined` fd) | fd <- classFDs]
                              where classFDs = fromMaybe [] (lookup cl fds)
                      in filterGenerics determined
                 sequence_ [ try (assume axioms fds ops pr p isRoot) | (pr, p) <- newAssumptions' ]

          state t = Tactic (\st -> (Progress st, st)) >>= t
          filterGenerics vs = Tactic (\st -> (Progress (), st { gvars = filter (`notElem` vs) (gvars st) }))

-- Utility function, used in assume and solve.  Given a requirement template and a new assumption,
-- computes any new requirements that arise from the assumption.  For example, given the requirement
-- template
-- > forall x y z, x < y, y < z => x < z.
-- and the new assumption
-- > t < 4
-- this function would compute two new requirement templates:
-- > forall z, 4 < z => t < z.
-- and
-- > forall x. x < t => x < 4.
applyRequirement :: Opacities -> PCon -> Pred -> RequirementTemplate -> Tactic (Either [RequirementTemplate] [(PCon, Pred)])
applyRequirement ops pr p (vs, qs, pcon)
    | inapplicable = noProgress
    | otherwise    = trace ("applyRequirement: " ++ intercalate ", " [ ppx p, ppx (vs, qs) ]) $
                     case qs of
                       [q] -> finish q
                       _   -> do newRqs <- catMaybes `fmap` mapM (expand qs) [0..length qs - 1]
                                 case newRqs of
                                   [] -> noProgress
                                   _  -> return (Left newRqs)


    where inapplicable = all (className p /=) (map className qs)
              where className (Pred cl _ _ _) = cl

          finish q =
              do (_, gkvs) <- generics
                 case match (vs, gkvs) p q of
                   Right s -> return (Right [(pcon', s ## q') | (q', pcon') <- pcon [pr "_"]])
                   Left _  -> noProgress

          expand qs i =
              do (_, gkvs) <- generics
                 case match (vs, gkvs) p (qs !! i) of
                   Right s -> return (Just (vars p ++ vs, s ## without i qs,
                                            \ps -> [(s ## qs', prs) | (qs', prs) <- pcon (insert i (pr "_") ps)]))
                   Left _ -> return Nothing

              where without 0 (x:xs) = xs
                    without n (x:xs) = x : without (n - 1) xs

                    insert 0 x ys     = x : ys
                    insert n x (y:ys) = y : insert (n - 1) x ys

----------------------------------------------------------------------------------------------------
-- A restricted clause is the result of comparing a goal predicate with an axiom conclusion under a
-- functional dependency, which occurs in both improvementFromAxioms and applyAxiom. This can be
-- either:
--
-- * Irrelevant, if the goal and conclusion do not match on the determining parameters;
-- * Confirming, if the goal matches the conclusion on the determining parameters and the conclusion
--   matches the goal on the the determined parameters; or,
-- * Contradicting, if the goal matches the conclusion on the determining parameters, but the
--   conclusion does not match the goal on the determined parameters, or the flags of the goal and
--   conclusion do not agree.
-- * Intersecting, if the goal and conclusion unify, but do not match, on the determining parameters.
--
-- The payloads and uses of the various states differ between the two uses of the type.

-- NOTES: restrict is used both in applyAxiom and in improvementFromAxioms/necessaryFromAssumptions.
-- These usages differ in their treatment of the positions outside the functional dependency.  In
-- the former case, if the goal differs from the conclusion at one of these positions, the
-- conclusions is irrelevant, whereas in the latter case they play no role at all.
--
--   The treatment of Contradicting is currently broken.  Suppose that we have
--
--    C a b c | a ~> b
--    C Int Float Bool.
--
-- And then we provide the query C Int Bool t.  The instance above is being treated as Intersecting,
-- depending on the additional condition [t :-> Bool].  But this is not the case: contradiction can
-- be established on the basis of the functional dependency alone.

data Restricted t u v w = Irrelevant | IntersectingConfirming t | IntersectingContradicting u | Confirming v | Contradicting w

----------------------------------------------------------------------------------------------------
-- Debugging nonsense:

instance (PP t, PP u, PP v, PP w) => PP (Restricted t u v w)
    where pp _ (Irrelevant) = "Irr"
          pp _ (IntersectingConfirming x) = "IsectConfirm " ++ ppx x
          pp _ (IntersectingContradicting x) = "IsectContra " ++ ppx x
          pp _ (Confirming x) = "Confirm " ++ ppx x
          pp _ (Contradicting x) = "Contra " ++ ppx x

instance PP (AxId, [Type], Subst, [Pred])
    where pp _ (_, _, s, ps) = ppx s ++ " if " ++ ppx ps

instance PP t => PP (Maybe t)
    where pp _ Nothing  = "Nothing"
          pp _ (Just x) = "Just " ++ ppx x

----------------------------------------------------------------------------------------------------

restrict :: ((Pred -> Pred -> Tactic Subst) -> FunDep -> (Pred -> Pred -> Tactic Subst)) ->
            Pred -> Pred -> FunDep ->
            Tactic (Restricted (Subst, Subst, Subst) (Subst, Subst) (Subst, Subst) Subst)
restrict mod goal conclusion fd
    | flag goal == flag conclusion =
        conditional ((matches `mod` fd) goal conclusion)
                    (\s -> conditional ((unifiesGeneric `atDetermined` fd) (s ## conclusion) goal)
                                       (\impr -> let (impr', subst') = (impr, empty) -- partitionSubst (vars goal) impr
                                                 in  return (Confirming (subst' `compose` s, impr')))
                                       (conditional ((unifies `atDetermined` fd) (s ## conclusion) goal)
                                                    (\impr -> let (cond, subst) = partitionSubst (vars goal) s
                                                                  (impr', subst') = (impr, empty) -- partitionSubst (vars goal) impr
                                                              in  return (IntersectingConfirming (subst' `compose` subst, cond `compose` impr', empty)))
                                                    (return (Contradicting s))))
                    (conditional ((unifies `mod` fd) goal conclusion)
                                 (\s -> conditional ((unifies `atDetermined` fd) (s ## conclusion) goal)
                                                    (\impr -> let (cond, subst) = partitionSubst (vars goal) s
                                                                  Right cond' = cond `under` subst
                                                              in return (IntersectingConfirming (subst, cond', impr)))
                                                    (let (cond, subst) = partitionSubst (vars goal) s
                                                     in  return (IntersectingContradicting (subst, cond))))
                                 (return Irrelevant))
    | otherwise =
        conditional ((matches `mod` fd) (invert goal) conclusion)
                    (\subst -> conditional ((unifiesGeneric `atDetermined` fd) (subst ## conclusion) (invert goal))
                                           (\impr -> return (Contradicting subst))
                                           (return (Confirming (subst, empty))))
                    (conditional ((unifies `mod` fd) (invert goal) conclusion)
                                 (\s -> let (cond, subst) = partitionSubst (vars goal) s
                                        in  return (IntersectingContradicting (subst, cond)))
                                 (return Irrelevant))

restrictClause :: ((Pred -> Pred -> Tactic Subst) -> FunDep -> (Pred -> Pred -> Tactic Subst)) ->
                  FunDep -> Pred -> (AxId, [Type], Qual Pred) ->
                  Tactic (Restricted Subst [Pred] (AxId, [Type], Subst, [Pred]) [Pred])
restrictClause mod fd goal (name, ts, hypotheses :=> conclusion) =
    do r <- restrict mod goal conclusion fd
       return (case r of
                 Irrelevant -> Irrelevant
                 IntersectingConfirming (subst, cond, impr) -> IntersectingConfirming impr
                 IntersectingContradicting (subst, cond) -> IntersectingContradicting (subst ## hypotheses)
                 Confirming (subst, impr)
                     | any (`elem` (vars hypotheses)) (vars (goal `atDetermining` fd)) ->
                         IntersectingConfirming impr
                     | otherwise ->
                         Confirming (name, subst ## ts, impr, subst ## hypotheses)
                 Contradicting subst -> Contradicting (subst ## hypotheses))

----------------------------------------------------------------------------------------------------
-- Given a set of assumptions ps, necessaryFromAssumptions ... ps returns the improvements and other
-- assumptions that must hold for ps to hold.  These arise from comparing the ps against the known
-- axioms.  Given some assumption p, if there is an axiom alpha such that alpha restricted to p is
-- "p if P; p'" such that p' contradicts p, we know that p can only hold if the hypotheses P hold.
-- This comparison can also be done modulo functional dependencies; for example, given the axiom
-- > F t Int if P; F t u fails.
-- we can conclude that the assumption F t u can only hold first, if the hypothese P hold, and
-- second, under the improving substitution [Int/u].
--
-- This feature is still limited in several ways.  First, given an axiom like:
-- > C Int; C t fails.
-- it will not conclude from an assumption C t that [Int/t] is an improving substitution.  Second,
-- given an axiom like:
-- > C t if D t; C t fails if E t.
-- it will not conclude D t from the assumptions C t, E t, even though, given the assumption E t,
-- the assumption D t must also hold.

necessaryFromAssumptions :: Axioms -> FunDeps -> Opacities -> [(PCon, Pred)] -> Tactic (Subst, [(PCon, Pred)])
necessaryFromAssumptions axioms fds ops ps = loop ps [] (empty, [])
    where loop [] _ (impr, added) = return (impr, added)
          loop ((pcon, p):ps) done (impr, added)
              | p `elem` done = loop ps done (impr, added)
              | otherwise     = do (impr', added') <- necessaryFromAssumption (pcon, p)
                                   case concatSubsts [impr', impr] of
                                     Nothing -> return (empty, []) -- Equivalent to assuming false---do something more interesting here.  (Exit?)
                                     Just impr'' -> loop (map (impr ##) (ps ++ added ++ [(pcon, p)]))
                                                         (map (impr ##) (p : done))
                                                         (impr'', added' ++ impr ## added)

          necessaryFromAssumption (pcon, goal@(Pred className ts _ _)) =
              do axioms' <- mapM (instantiateAxiom ops) (filter (\(Ax _ (Forall _ (_ :=> Pred className' _ _ _) : _)) -> className == className') axioms)
                 necessaryFrom axioms'

              where defaultFD = [0..length ts - 1] :~> []
                    classFDs  = fromMaybe [defaultFD] (lookup className fds)

                    necessaryFrom [] = return (empty, [])
                    necessaryFrom axioms =
                        do (ss, pss) <- (unzip . catMaybes) `fmap` mapM isApplicable axioms
                           case concatSubsts ss of
                             Nothing -> error (unlines ("Whoops: inconsistent substitutions in necessaryFromAssumptions." : map ppx ss))
                             Just s  -> return (s, concat pss)

                    isApplicable (name, clauses) =
                        do restricted <- mapM (\fd -> mapM (restrictClause modFD fd goal) clauses') classFDs
                           let assumptions = map collectAssumptions restricted
                           return (mergeAssumptions =<< sequence assumptions)
                        where clauses' = [(nameFor i, ts, qp) | (i, (ts, qp)) <- zip [0..] clauses]
                              nameFor i | length clauses == 0 = AxId (nameFrom name) Nothing
                                        | otherwise           = AxId (nameFrom name) (Just i)

                    collectAssumptions tries =
                        case filtered of
                          [Confirming (axid, ts, s, ps), Contradicting []] ->
                              let patFor i pid = PFrom (Pat axid ts [nameFor i | i <- [0..length ps - 1]]) (pcon "_") (PAssump pid (nameFor i))
                              in Just (s, [(patFor i, p) | (i, p) <- zip [0..] ps])
                          _ ->
                              trace (unlines (map ppx filtered)) Nothing
                        where filtered = [t | t <- tries, relevant t]
                              relevant Irrelevant = False
                              relevant _          = True

                              nameFor i = toId ('x' : show i)

                    mergeAssumptions []        = Nothing
                    mergeAssumptions [(s, ps)] = Just (s, ps)
                    mergeAssumptions pairs     =
                        do s <- concatSubsts ss
                           let pss' = s ## pss
                           guard (all (\ps -> map snd (head pss') == map snd ps) (tail pss'))
                           return (s, head pss')
                        where (ss, pss) = unzip pairs

----------------------------------------------------------------------------------------------------
-- improvementFromAxioms axioms fds goal computes an improvement to the variables in goal, without
-- assuming which, if any, axiom may solve goal.  This is useful both for computing improvements
-- from assumptions and for finding improvements from predicates that cannot yet be solved.  An
-- example of the latter, from tests/solver/tests/impr1:
--
-- > C t u v | t ~> u.
-- > D u v | u ~> v.
-- >
-- > C Int Float Bool.
-- > C Int Float Char.
-- > D Float Bool.
-- >
-- > C Int u v, D u v?
--
-- The solver does not have enough information to discharge the predicate 'C Int u v': parameter 'v'
-- is not determined.  However, the solver does have enough information to improve variable 'u';
-- this, in turn, allows the predicate 'D u v' to be discharged, improving variable 'v' and allowing
-- predicate 'C Int u v' to be discharged.  In this case, the solution is that the predicates hold
-- under the improvement [Float/u, Bool/v].

improvementFromAxioms :: Axioms -> FunDeps -> Opacities -> Pred -> Tactic Subst
improvementFromAxioms _ _ _ (Pred _ _ Exc _) = return empty
improvementFromAxioms axioms fds ops goal@(Pred className ts _ _) =
    do axioms' <- mapM (instantiateAxiom ops) (filter (\(Ax _ (Forall _ (_ :=> Pred className' _ _ _) : _)) -> className == className') axioms)
       improvementFrom axioms'

    where classFDs = fromMaybe [] (lookup className fds)

          -- improvementFrom fds collects the improvements from the given functional dependencies
          -- and instantiated axioms.  For a given functional dependency, we return an improvement
          -- iff that improvement results from all the matching axioms, and is consistent with the
          -- improvement resulting from the intersecting axioms.  We do not include improvements
          -- that arise only from intersecting axioms, or are contradicted by intersecting axioms.
          -- Note that we treat a predicate which matches a goal, but in which the hypotheses
          -- constrain the determining type variables, as an intersection.
          --
          -- For example (tests/solver/tests/3):
          --
          -- > C t u v | t u ~> v.
          -- > C t t True; C t u False.
          -- > C x y z?
          --
          -- The goal predicate does not match the first clause of the instance chain; thus, the
          -- only improving substitution from matching clauses is [False/z].  However, because the
          -- goal predicate and the first clause do intersect ([t/x, t/y]), and that clause gives
          -- rise to a different improvement ([True/z]), we compute no improvement for 'z' in this
          -- case.
          --
          -- improvementFrom begins by attempting to find improvements for each functional
          -- dependency.  The resulting tries are discarded either if the goal was inconsistent with
          -- one of the declared axioms, or if matching resulting improvements are inconsistent with
          -- each other, or with the intersecting improvements.  Finally, if the improvements from
          -- the different functional dependencies are consistent, the resulting substitutions are
          -- composed and returned.

          improvementFrom [] = return empty
          improvementFrom axioms =
              do restricted <- mapM (\fd -> mapM (restrictClause atDetermining fd goal) clauses) classFDs
                 let imprs = catMaybes (map (collectSubsts >=> mergeSubsts) restricted)
                 case mergeSubsts (unzip imprs) of
                   Just (matching, _) -> return (productive matching)
                   _                  -> return empty

              where (varss, clauses) = unzip [(ts, (axid name (length instQPreds) i, ts, qp)) |
                                                (i, (name, instQPreds)) <- zip [0..] axioms,
                                                (ts, qp@(_ :=> Pred _ _ Inc _)) <- instQPreds]

                    axid name 0 i = AxId (nameFrom name) Nothing
                    axid name _ i = AxId (nameFrom name) (Just i)

                    newVars = concat varss

                    collectSubsts = foldr f (Just ([], []))
                        where f _ Nothing                                                  = Nothing
                              f (Contradicting _) _                                        = Nothing
                              f (IntersectingContradicting _) _                            = Nothing
                              f Irrelevant x                                               = x
                              f (Confirming (_, _, s, [])) (Just (matching, intersecting)) = Just (s : matching, intersecting)
                              f (Confirming (_, _, s, ps)) (Just (matching, intersecting)) = Just (matching, s : intersecting)
                              f (IntersectingConfirming s) (Just (matching, intersecting)) = Just (matching, s : intersecting)

                    mergeSubsts (matchings, intersectings) =
                        do matching <- concatSubsts matchings
                           intersecting <- concatSubsts intersectings
                           guard (consistent matching intersecting)
                           return (matching, intersecting)

                    -- In some cases, it's possible to find "improvements" that don't actually
                    -- provide any new information.  Consider the axioms
                    -- > Mult t u v | t u ~> v.
                    -- > Mult Z b b.
                    -- > Mult (S a) b d if Mult a b c, Add a c d.
                    -- and the query
                    -- > Mult P4 P2 x?
                    -- The second axiom matches the query, under the substitution [a :-> P3, b :->
                    -- P2], but the resulting improvement, [x :-> d'] for some fresh identifier d',
                    -- conveys no new information.  Further, this improvement could be done forever
                    -- (with new, fresh d's), leading to difficulties in solver termination.
                    -- Therefore, we identify these unproductive improvements and eliminated them
                    -- here.
                    productive (S ks bs) = S ks (filter (\(_ :-> v) -> v `notElem` newVars) bs)

----------------------------------------------------------------------------------------------------
-- applyAxiom attempts to apply the available axioms to the current goal.  Should we find a matching
-- axiom, we assume that axioms applies, and introduce corresponding functional dependency
-- assumptions.  This may be a stronger set of assumptions than can arise from simply assuming the
-- goal holds; for example, given the program:
-- > F t u | t ~> u.
-- > F t True if C t; F t False.
-- and the goal
-- > F Int t?
-- simply assuming the goal holds gives no improvement for 't' (as it could be either True or
-- False).  However, assuming that the first clause of the axiom applies gives the improvement
-- [True/t]

applyAxiom :: Axioms -> FunDeps -> Opacities -> Tactic ()
applyAxiom axioms fds ops = node applyAxiom'
    where applyAxiom' (Goal name goal isRoot Nothing) = guardAxiomApplication fds goal >> applyTo name goal isRoot
          applyAxiom' _                               = noProgress

          applyTo name goal@(Pred className ts _ loc) isRoot =
              do axioms' <- mapM (instantiateAxiom ops) (filter (\(Ax _ (Forall _ (_ :=> Pred className' _ _ _) : _)) -> className == className') axioms)
                 cs      <- catMaybes `fmap` mapM isApplicable (catAxioms axioms')
                 traceIf (not (null cs) && null (filter (\(_, _, _, _, conditions) -> trivial conditions) cs))
                         ("No progress in applyAxiom: all applicable clauses had non-trivial conditions.\n" ++
                          unlines [ppx ax ++ "[" ++ intercalate "," (map ppx ts) ++ "] " ++
                                   ppx spin ++ " <= " ++ intercalate ", " (map ppx hypotheses) ++
                                   " if " ++ ppx conditions
                                   | (ax, ts, hypotheses, spin, conditions) <- cs])
                         (return ())
                 guard (not (null (filter (\(_, _, _, _, conditions) -> trivial conditions) cs)))
                 case cs of
                   -- Shortcut case for axioms with empty hypotheses.  In this case, it is safe to
                   -- ignore both the hypotheses (as they are trivially satisfied) and the
                   -- alternatives (as the present clause cannot be isDisproved).
                   ((ax, ts, [], spin, conditions) : _)
                       | trivial conditions ->
                           case [impr | (_, _, impr) <- conditions, not (isEmpty impr)] of
                             impr : _ -> do trace ("Computed improvement in applyAxiom from axiom " ++ ppx ax ++ " applied to " ++ ppx goal) (bind impr)
                                            update (Complete name goal spin [] (PAx name ax ts [] []))
                             _ -> update (Complete name goal spin [] (PAx name ax ts [] []))
                   _ -> do checkDepth
                           (cnode : cnodes) <- mapM new [Clause name goal spin ax ts conditions (Left (map setLocation hypotheses)) |
                                                         (ax, ts, hypotheses, spin, conditions) <- cs]
                           elseNode <- new (Chain [] cnode cnodes)
                           update (Goal name goal isRoot (Just elseNode))

              where defaultFD = [0..length ts - 1] :~> []
                    classFDs  = fromMaybe [defaultFD] (lookup className fds)

                    setLocation (Pred cl ts f _) = Pred cl ts f loc

                    trivial = null .||. any (isEmpty . snd3)
                        where snd3 (_, x, _) = x

                    -- As we know that axioms do not overlap, we can treat all the axioms that match
                    -- a given predicate as one long instance chain: should any clause solve the
                    -- given predicate, we know that no later clause in the mega-chain would have.
                    catAxioms [] = []
                    catAxioms ((axid, rules) : axs) =
                        case rules of
                          [(ts, qp)] -> (AxId (nameFrom axid) Nothing, ts, qp) : catAxioms axs
                          _          -> [(AxId (nameFrom axid) (Just n), ts, qp) | (n, (ts, qp)) <- zip [0..] rules] ++ catAxioms axs

                    isApplicable (ax, typeArgs, hypotheses :=> conclusion) =
                        do ts <- restricted
                           return (case ts of
                                     Irrelevant ->
                                         Nothing
                                     IntersectingConfirming (subst, conditions) ->
                                         Just (ax, subst ## typeArgs, subst ## hypotheses, Proving, [(vs, cond, impr) | (cond, impr) <- conditions])
                                     IntersectingContradicting (subst, conditions) ->
                                         Just (ax, subst ## typeArgs, subst ## hypotheses, Disproving, [(vs, cond, empty) | cond <- conditions])
                                     Confirming (subst, impr) ->
                                         Just (ax, subst ## typeArgs, subst ## hypotheses, Proving, [(vs, empty, impr)])
                                     Contradicting subst ->
                                         Just (ax, subst ## typeArgs, subst ## hypotheses, Disproving, []))

                        where vs = [v | TyVar v <- typeArgs]

                              restricted = case flag conclusion of
                                        Exc -> do t <- restrict modFD goal conclusion defaultFD
                                                  return (concatTries [t])
                                        Inc -> do ts <- mapM (restrict modFD goal conclusion) classFDs
                                                  let r = concatTries ts
                                                  trace (unlines (["In applyAxiom:",
                                                                   "    Comparing " ++ ppx (hypotheses :=> conclusion) ++ " to " ++ ppx goal] ++
                                                                  ["    " ++ ppx (className, [fd]) ++ ":" ++ ppx restricted | (fd, restricted) <- zip classFDs ts] ++
                                                                  ["    Giving " ++ ppx r]))
                                                        (return r)
                                                  -- return (concatTries ts)

                              -- Combining tries works differently than combining candidates: as
                              -- long as a clause contradicts or matches under one functional
                              -- dependency, we consider it to be matching; it is only considered
                              -- intersecting if it is intersecting under all functional
                              -- dependencies.  For example, given
                              -- > C t u | t ~> u, u ~> t.
                              -- > C t t.
                              -- and the query
                              -- > C t Int?
                              -- the goal intersects the query when considered under the first
                              -- functional dependency, but matches under the second.

                              -- TODO: I suspect the above comment is misguided; it's also out of date (what is a candidate?).

                              concatTries :: [Restricted (Subst, Subst, Subst) (Subst, Subst) (Subst, Subst) Subst] ->
                                             (Restricted (Subst, [(Subst, Subst)]) (Subst, [Subst]) (Subst, Subst) Subst)
                              concatTries ts
                                  | null ts' = Irrelevant
                                  | otherwise = merge ts'
                                  where ts' = filter notIrrelevant ts
                                        notIrrelevant Irrelevant = False
                                        notIrrelevant _          = True

                                        merge [IntersectingConfirming (subst, cond, impr)] =
                                            IntersectingConfirming (subst, [(cond, impr)])
                                        merge [IntersectingContradicting (subst, cond)] =
                                            IntersectingContradicting (subst, [cond])
                                        merge [Confirming (subst, impr)] =
                                            Confirming (subst, impr)
                                        merge [Contradicting subst] =
                                            Contradicting subst
                                        merge (IntersectingConfirming (subst, cond, impr) : rest) =
                                            case merge rest of
                                              IntersectingConfirming (subst', conditions) ->
                                                  IntersectingConfirming (subst `compose` subst', (cond, impr) : conditions)
                                              Confirming (subst', impr') ->
                                                  IntersectingConfirming (subst `compose` subst', [(cond, impr), (empty, impr')])
                                                  -- case cond `under` impr' of
                                                  --   Right cond' | isEmpty cond' -> Confirming (subst', impr')
                                                  --   _                           -> IntersectingConfirming (subst `compose` subst', [(cond, impr), (empty, impr')])
                                              -- TODO: should there be a case parallel to the
                                              -- Confirming/IntersectConfirming case below?  Does the ordering of
                                              -- instance chains come in?
                                              -- NOW: there is.
                                              t -> t
                                        merge (IntersectingContradicting (subst, cond) : rest) =
                                            case merge rest of
                                              Contradicting s                           -> Contradicting s
                                              IntersectingContradicting (subst', conds) -> IntersectingContradicting (subst `compose` subst', cond : conds)
                                              _                                         -> IntersectingContradicting (subst, [cond])
                                        merge (Contradicting subst : rest) =
                                            Contradicting subst
                                        merge (Confirming (subst, impr) : rest) =
                                            case merge rest of
                                              IntersectingConfirming (subst', conditions) ->
                                                  IntersectingConfirming (subst `compose` subst', (empty, impr) : conditions)
                                                  -- let first f (x, y) = (f x, y)
                                                  --     fromRight (Right x) = x
                                                  --     conditions' = filter (not . isEmpty . fst) $ map (first (fromRight . (`under` impr))) conditions in
                                                  -- if null conditions'
                                                  -- then Confirming (subst, impr)
                                                  -- else IntersectingConfirming (subst `compose` subst', (empty, impr) : conditions)
                                              Confirming (subst', impr') -> Confirming (subst `compose` subst', impr `compose` impr')
                                              r                          -> r


-- 'checkCondition cond' returns 'Nothing' if 'cond' is inconsistent with the current substitution,
-- or 'Just (remaining, binding)', where 'remaining' is the unconfirmed part of the condition and
-- 'binding' can be added to the current substitution.  For example, consider a call to
-- 'checkCondition [t :-> S u, v :-> S w]' with current substitution [t :-> 4, v :-> x].  In this
-- case, we would expect checkCondition to return the remaining condition [x :-> S w], and the
-- binding [u :-> 3].
checkCondition :: [TyId] -> Subst -> Tactic (Maybe (Subst, Subst))     -- RETURN VALUE: (condition, binding)
checkCondition ws (S ks cond) =
    do checked <- mapM (trail . check) cond
       case unzip `fmap` sequence checked of
         Nothing -> return Nothing
         Just (remainings, bindings)
             | Just remaining <- concatSubsts remainings, Just binding <- concatSubsts bindings ->
                 return (Just (remaining, binding))
             | otherwise ->
                 return Nothing

    where check (v :-> t) tr =
              case findBinding v (substitution tr) of
                Nothing -> return (Just (S ks [v :-> t], empty))
                Just mu ->
                    let u = plain mu
                    in  conditional (matches u (substitution tr ## t))
                                    (\s -> return (Just (partitionSubst (filter (`notElem` ws) (domain s)) s)))
                                    (conditional (unifies u (substitution tr ## t))
                                                 (\s -> return (Just (partitionSubst (filter (`notElem` ws) (vars u)) s)))
                                                 (return Nothing))

-- Conditions are now stored in (condition, improvement) pairs; given a list l of such pairs, this
-- checkConditions returns Just l' if all of the conditions are consistent with the current
-- hypotheses, or Nothing if any of them not.
checkConditions :: [([TyId], Subst, Subst)] -> Tactic (Maybe (Subst, [([TyId], Subst, Subst)]))  -- RETURN VALUE: (binding, conditions)
checkConditions ps =
    do cs <- mapM (\(tyids, cond, _) -> checkCondition tyids cond) ps
       case sequence cs of
         Nothing -> return Nothing
         Just cs' -> case concatSubsts (map snd cs') of
                       Nothing -> return Nothing
                       Just binding -> return (Just (binding, [(tyids, cond, impr) | ((cond, _), (tyids, _, impr)) <- zip cs' ps]))

-- Collapses subtrees, if possible.  This can be either because all the subgoals have been proven
-- (in which case the original goal is proven), because one subgoal is disproven (in which case the
-- original axiom did not apply), or because no further progress can be made.
collapse :: Tactic ()
collapse = explainHeader "collapse" (node collapse')
    where collapse' (Goal name goal _ (Just (Tree (Complete _ _ spin [] pr) _))) =
              update (Complete name goal spin [] pr)
          collapse' (Goal _ _ _ (Just t))
              | isStuck n     = tree collapseStuck
              | isExhausted n = tree (replace . Exhausted)
              | otherwise     = noProgress
              where n = nodeFrom t
          collapse' node@(Clause name goal spin axid typs conditions (Right subtrees))
              | all isProved subgoals =
                  update (Complete name goal spin conditions (PClause name axid typs (map proof subgoals)))
              | all (isProved .||. isExhausted) subgoals =
                  tree (replace . Exhausted)          -- ?? Why replace and not update?
              | all (isProved .||. isExhausted .||. isStuck) subgoals =
                  tree collapseStuck
              | otherwise =
                  do case findIndex isDisproved subgoals of
                       Nothing -> return ()
                       Just i  -> do invalidate
                                     trace ("Backtracking at " ++ showShort node)
                                           (update (Complete name goal spin
                                                             []                                          -- Conditions are irrelevant to a PSkip: even if the condition
                                                                                                         -- were satisfied, the clause would still not apply.
                                                             (PSkip axid (i, proof (subgoals !! i)))))   -- TODO: PSkip is not actually a proof of the goal either way.
              where subgoals = map nodeFrom subtrees
                    childDependencies = map (dependsOn . metaFrom) subtrees
          collapse' (Computed name goal spin vs pbuilder (Right subtrees))
              | all isProved subgoals = pbuilder subproofs `orElse` tree (replace . Exhausted)
              | all (isProved .||. isExhausted) subgoals = tree (replace . Exhausted)
              | all (isProved .||. isExhausted .||. isStuck) subgoals = tree collapseStuck
              | otherwise = tree (replace . Exhausted)
              where subgoals = map nodeFrom subtrees
                    subproofs = [p | Complete { proof = p } <- subgoals]
          collapse' (Chain passed current rest) =
              do (current' : passed') <- mapM updateCondition (current : passed)
                 uvars <- Tactic (\st -> (Progress (uvars st), st))
                 solved uvars (current' : passed') `orElse` nextBranch passed' current' rest
              where updateCondition (Tree (Complete name goal spin conditions p) meta) =
                        do updatedCond <- checkConditions conditions
                           updatedImpr <- sequence `fmap` trail (\tr -> return [impr `under` substitution tr | (_, _, impr) <- conditions])
                           case (updatedCond, updatedImpr) of
                             (Nothing, _) -> return (Tree (Complete name goal spin [] PInapplicable) meta)
                             (Just (binding, conditions'), Left _) ->
                                 do bind binding
                                    return (Tree (Complete name goal Disproving [(tyids, cond, empty) | (tyids, cond, _) <- conditions'] p) meta)
                             (Just (binding, conditions'), Right improvements') ->
                                 (do bind binding
                                     return (Tree (Complete name goal spin [(tyids, cond, impr) | ((tyids, cond, _), impr) <- zip conditions' improvements'] p) meta)) `orElse`
                                 trace ("Unable to add binding " ++ ppx binding ++ "\nupdating conditions " ++
                                        intercalate ", " [ppx condition ++ " -> " ++ ppx impr | (_, condition, impr) <- conditions])
                                       noProgress
                    updateCondition t = return t

                    solved uvars cs = loop [] [] []  (reverse (map nodeFrom cs))
                        where loop skips casesProving casesDisproving (Complete { proof = PInapplicable } : rest) =
                                  loop skips casesProving casesDisproving rest

                              loop skips casesProving casesDisproving (t@(Complete { proof = PSkip{} }) : rest) =
                                  loop (t:skips) casesProving casesDisproving rest

                              loop skips casesProving casesDisproving ((Complete name goal Proving conditions pr@(PClause _ axid typs ps)) : rest)
                                  | not (null casesDisproving') = trace ("Stuck! Disproving cases: " ++ unlines["    " ++ ppx condition ++ " => " ++ ppx p | (_, condition, _, p) <- casesDisproving']) $
                                                                  noProgress
                                  | not (null conditions) && all (\(_, cond, _) -> not (isEmpty cond)) conditions =
                                      let (tyids, cond, impr) = head conditions
                                      in  loop skips ((tyids, cond, impr, pr) : casesProving) casesDisproving rest
                                  | null casesProving' = let impr = head [impr | (_, cond, impr) <- conditions, isEmpty cond]
                                                         in  (do bind impr
                                                                 update (Complete name goal Proving [] (PAx name axid typs (skipsFrom axid skips) ps))) `orElse`
                                                             update (Complete name goal Disproving [] (PAx name axid typs (skipsFrom axid skips) ps))
                                  | all respectsUniformity casesProving' =
                                      let impr | null conditions = empty
                                               | otherwise = head [impr | (_, cond, impr) <- conditions, isEmpty cond]
                                      in  update (Complete name goal Proving [] (PCases name (reverse ((empty, impr, PClause name axid typs ps) : [(cond, impr, p) | (_, cond, impr, p) <- casesProving']))))

                                  where casesProving' = filter (not . excluded) casesProving
                                        casesDisproving' = filter (not . excluded) casesDisproving
                                        conditions' | not (null trivial) = trivial
                                                    | otherwise          = conditions
                                            where trivial = filter (\(_, cond, _) -> isEmpty cond) conditions
                                        excluded (_, cond', _, _) =
                                            all (\(_, cond, impr) -> succeeded (cond' `under` cond) && failed (cond' `under` impr)) conditions'
                                            where succeeded (Right _) = True
                                                  succeeded _         = False
                                                  failed (Left _)     = True
                                                  failed _            = False

                              loop skips casesProving casesDisproving (Complete name goal Disproving conditions pr@(PClause _ axid typs ps) : rest)
                                  | not (null casesProving) = noProgress
                                  | not (null conditions) && all (\(_, cond, _) -> not (isEmpty cond)) conditions =
                                      let (tyids, cond, _) = head conditions
                                      in  loop skips casesProving ((tyids, cond, empty, pr) : casesDisproving) rest
                                  | null casesDisproving = update (Complete name goal Disproving [] (PAx name axid typs (skipsFrom axid skips) ps))
                                  | otherwise = update (Complete name goal Disproving []
                                                          (PCases name (reverse ((empty, empty, PClause name axid typs ps) : [(cond, impr, p) | (_, cond, impr, p) <- casesDisproving]))))

                              loop _ _ _ _ = noProgress

                              respectsUniformity (_, _, impr, _) = all (`notElem` uvars) (domain impr)

                              skipsFrom (AxId name _) = go []
                                  where go ss [] = ss
                                        go ss (Complete _ _ _ _ (PSkip (AxId name' _) skip) : rest)
                                            | name == name' = go (skip : ss) rest
                                            | otherwise     = go ss rest
                                        go ss _ = error "Solver.Main:375"

                    nextBranch passed' current' rest
                        | (isProved .||. isDisproved) currentNode =
                            case rest of
                              [] -> updateStuck
                              (r:rs) -> update (Chain (current' : passed'') r rs)
                        | isStuck currentNode = updateStuck
                        | isExhausted currentNode =
                            if all (isSkipped . nodeFrom) passed'
                            then do update (Chain passed'' current' rest)
                                    tree (replace . Exhausted)
                            else updateStuck
                        | otherwise =
                            update (Chain passed'' current' rest)
                        where passed'' = filter (isApplicable . nodeFrom) passed'
                              isApplicable (Complete _ _ _ _ PInapplicable) = False
                              isApplicable _                                = True

                              currentNode = nodeFrom current
                              updateStuck = do update (Chain passed'' current' rest)
                                               tree collapseStuck
                              isSkipped (Complete _ _ _ _ PSkip{}) = True
                              isSkipped _                          = False
          collapse' (Alternatives subtrees)
              | (t:_) <- proved          = replace t
              | (t:_) <- disproved       = replace t
              | any isStuck subnodes     = tree collapseStuck
              | all isExhausted subnodes = tree (replace . Exhausted)
              where subnodes  = map nodeFrom subtrees
                    proved    = filter isProved subnodes
                    disproved = filter isDisproved subnodes

          -- Nodes become unstuck if any progress has been made since they got stuck; this means
          -- that we need to be able to unstick a node not just based on its own timestamp but also
          -- those of its subtrees.
          collapseStuck t@(Tree node meta) = trace ("Collapsing stuck node " ++ showShort node) $
                                             do n <- now
                                                replaceT (Tree (Stuck t) meta { lastUpdated = minimum (n : times) })
              where ts    = children node
                    times = [lastUpdated (metaFrom t) | t <- ts, isStuck (nodeFrom t)]

stuck :: Tactic ()
stuck = tree stuck'
    where stuck' (Tree (Stuck _) _) = return ()
          stuck' t                  = do n <- now
                                         trace (showShort (nodeFrom t) ++ " stuck at " ++ show n) (update (Stuck t))

solved :: Tactic ()
solved = node (\n -> if isSolving n then noProgress else return ())

exhaust :: Tactic ()
exhaust = tree (replace . Exhausted)

-- Exhausts a goal in which either an argument in an opaque position is not a type variable, or is
-- but is not treated opaquely.  There is some cunning here: checkOpacity is called before
-- applyTrail, so that refinements of opaque variables do not have to be treated separately than
-- refinements of transparent variables.  However, it is possible that a predicate fails the opacity
-- check, yet has been assumed.  In that case, we still discharge the goal.
checkOpacity :: FunDeps -> Opacities -> Tactic ()
checkOpacity fds ops = node check
    where check (Goal name goal@(Pred cl ts _ _) _ Nothing) =
              do ovs <- opaqueVariables
                 when (any (not . isTyVar) (filterIdxs opaquePositions ts) || any (`notElem` ovs) (ovars ops goal)) $
                      do try (applyTrail fds)
                         solved `orElse` do addToTrail goal (\pid -> PAssump pid name)
                                            exhaust
              where opaquePositions   = fromMaybe [] (lookup cl ops)
                    isTyVar (TyVar _) = True
                    isTyVar _         = False
          check _ =
              return ()

----------------------------------------------------------------------------------------------------

-- consider reactivating a previously stuck tree if there have been new assumptions since last time
-- we were here.
activate :: Tactic ()
activate = tree activate'
    where activate' (Tree (Stuck t) meta) =
              do n <- now
                 if lastUpdated meta < n
                    then trace ("Activating " ++ showShort (nodeFrom t) ++ " (" ++ show (lastUpdated meta) ++ " < " ++ show n ++ ")") $
                         replaceT t
                    else noProgress
          activate' _ = noProgress

-- expand tries to find the leftmost leaf of the current node and "expand" it into a subtree.
expand :: Axioms -> FunDeps -> Opacities -> Tactic ()
expand axioms fds ops = explainHeader "expand" loop
    where loop = try activate >> node expand'

          -- goal with no proof in progress.
          expand' (Goal name g _ Nothing) =
              do try (checkOpacity fds ops)
                 try (applyTrail fds)
                 solved `orElse`
                     do try (assumeGoal axioms fds ops)
                        solveByOracles `orElse` applyAxiom axioms fds ops `orElse` stuck

          -- goal with proof already in progress.
          expand' (Goal _ g _ (Just _)) =
              do try (applyTrail fds)
                 solved `orElse`
                     (down >> try loop)

          -- Clause with condition, but no hypotheses:
          expand' (Clause name goal spin ax ts conditions (Left [])) =
              do updated <- checkConditions conditions
                 case updated of
                   Nothing -> update (Complete name goal spin [] PInapplicable)
                   Just (s, conditions') ->
                       do bind s
                          update (Complete name goal spin conditions' (PClause name ax ts []))

          -- Clause with hypotheses but no condition (i.e., not part of a proof by cases):
          expand' (Clause name goal spin ax ts [] (Left hypotheses)) =
              do simpl <- Tactic isSimplification -- (True indicates that the next clause is guaranteed to fail)
                 names <- replicateM (length hypotheses) (fresh "g")
                 subgoals <- mapM new [ Goal name goal False Nothing | (name, goal) <- zip names hypotheses ]
                 update (Clause name goal spin ax ts [] (Right subgoals))
                 down >> try loop
              where isSimplification st =
                      case here st of
                        Cursor (NodeP (Chain _ _ (Tree Clause{spin = Disproving, subtrees = Left []} _ : _)) _ _ _ _) _ ->
                             (Progress True, st)
                        _ -> (Progress False, st)

          -- Clause with condition, and hypotheses:
          expand' (Clause name goal spin ax ts conditions (Left hypotheses)) =
              do updated <- checkConditions conditions
                 case updated of
                   Nothing -> update (Complete name goal spin [] PInapplicable)
                   Just (s, conditions') ->
                       do bind s
                          names <- replicateM (length hypotheses) (fresh "g")
                          subgoals <- mapM new [ Goal name goal False Nothing | (name, goal) <- zip names hypotheses ]
                          update (Clause name goal spin ax ts conditions' (Right subgoals))
                          down >> try loop

          -- Clause with conditions and a proof in progress:
          expand' n@(Clause name goal spin ax ts conditions (Right subgoals)) =
              do updated <- checkConditions conditions
                 case updated of
                   Nothing -> update (Complete name goal spin [] PInapplicable)
                   Just (s, conditions') ->
                       do bind s
                          meta (stopIgnoring . childrenIntroduce)
                          update (Clause name goal spin ax ts conditions' (Right subgoals))
                          down >> try loop

          -- Proof by oracle, with hypotheses:
          expand' (Computed name goal spin vs pbuilder (Left hypotheses)) =
              do inputsRefined <- or `fmap` mapM tyvarRefined vs
                 if inputsRefined
                 then node resetGoal
                 else do names <- replicateM (length hypotheses) (fresh "g")
                         subgoals <- mapM new [ Goal name goal False Nothing | (name, goal) <- zip names hypotheses ]
                         update (Computed name goal spin vs pbuilder (Right subgoals))
                         down >> try loop

          -- Proof by oracle, already in progress:
          expand' (Computed _ _ _ vs _ (Right _)) =
              do inputsRefined <- or `fmap` mapM tyvarRefined vs
                 if inputsRefined
                 then node resetGoal
                 else down >> try loop

          -- A node with a previously completed proof that may have been invalidated by later
          -- refinements of the global substitution
          expand' (Complete name goal Proving [] p) =
              do conditionsRefined <- proofConditionsRefined p
                 if conditionsRefined
                 then do invalidate
                         b <- atRoot
                         replace (Goal name goal b Nothing)
                 else return ()
              where proofConditionsRefined (PAx _ _ _ _ prs) = or `fmap` mapM proofConditionsRefined prs
                    proofConditionsRefined (PCases _ cs) = or `fmap` mapM substRefined [cond | (cond, _, _) <- cs]
                    proofConditionsRefined (PComputedCases _ inputs _ _ _) = or `fmap` mapM tyvarRefined inputs
                    proofConditionsRefined (PRequired _ _ prs) = or `fmap` mapM proofConditionsRefined prs
                    proofConditionsRefined (PFrom pat pr pr') = liftM2 (||) (proofConditionsRefined pr) (proofConditionsRefined pr')
                    proofConditionsRefined _ = return False
                    substRefined (S _ bindings) = or `fmap` mapM tyvarRefined [v | (v :-> _) <- bindings]

          expand' (Complete name goal spin conditions p) =
              do updated <- checkConditions conditions
                 case updated of
                   Nothing -> update (Complete name goal spin [] PInapplicable)
                   Just (s, conditions') ->
                       do bind s
                          update (Complete name goal spin conditions' p)

          -- Remaining cases:
          expand' (Stuck _)     = noProgress
          expand' (Exhausted _) = noProgress
          expand' _             = down >> try loop

          -- A tactic that returns True if the substitution contains a binding for v
          tyvarRefined v = trail (\tr -> return (isJust (findBinding v (substitution tr))))

          atRoot = Tactic (\st -> case here st of
                                    Cursor (Forest _ _) _ -> (Progress True, st)
                                    _                     -> (Progress False, st))

          resetGoal (Goal name goal isRoot _) =
              do invalidate
                 replace (Goal name goal isRoot Nothing)
          resetGoal _ =
              up >> node resetGoal


advance :: FunDeps -> Opacities -> Tactic ()
advance fds ops = do try (node ignoreLocal)
                     node advance'
    where advance' (Complete _ _ Disproving [] pr) =
              (up `orElse` exit Failed) >> collapse >> advance fds ops
          advance' n =
              right `orElse` (up >> try collapse >> advance fds ops) `orElse` checkForest

          ignoreLocal (Clause { conditions = cs })
              | not (null cs) = meta (startIgnoring . childrenIntroduce)
          ignoreLocal _       = noProgress

-- checkForest, called at the right end of the forest, resets the cursor to the left-most tree on
-- which work can be done, or exits should no such tree exist.
checkForest :: Tactic ()
checkForest = do whileProgressing (try activate >> left)
                 try activate
                 cursor checkForest' >> arrive
    where checkForest' c@(Cursor (Forest [] trees') tree)
              | all isProved nodes = Exit (Done False)
              | all (isProved .||. isExhausted) nodes = Exit CantProgress
              | any isDisproved nodes = Exit Failed
              | otherwise = case break (isSolving . nodeFrom) trees of -- find first tree where there is (might be) work to do
                              (_, [])            -> Exit CantProgress
                              (stuck, here:rest) -> Progress (Cursor (Forest (reverse stuck) rest) here)
              where trees = tree : trees'
                    nodes = map nodeFrom trees
          checkForest' c = NoProgress

----------------------------------------------------------------------------------------------------
-- Solver entry points

data Query pred = Q { qAxioms          :: Axioms
                    , qFundeps         :: FunDeps
                    , qRequirements    :: Requirements
                    , qOpacities       :: Opacities
                    , qGenerics        :: ([TyId], [Id])
                    , qTransparents    :: [TyId]
                    , qUniformVariables :: [TyId]
                    , qHypotheses      :: [pred]
                    , qGoals           :: [pred] }

-- Answers contain both what progress the solver was able to make, and what goals (if any) remain
-- unsolved should the solver not have found a contradiction. This provides a simplification
-- function: the remaining goals are the simplification (in the sense that some solver progress has
-- already occurred) of the original goals.  However, the goals on which the solver got stuck may
-- not be valid simplification: in general, it is only safe to simplify C t to D t if (a) D t proves
-- C t, and (b) there is no other way to prove D t.

data Answer = AnsProved { evidence :: [(PId, Proof)]
                        , improvement :: Subst
                        , exFalso :: Bool
                        , nodes :: Int }
            | AnsStuck { evidence ::  [(PId, Proof)]
                       , remaining :: [(PId, Pred)]
                       , improvement :: Subst
                       , nodes :: Int }
            | AnsFailed { contradicted :: (PId, Pred)
                        , nodes :: Int }
              deriving Show

solve :: Query (PId, Pred) -> Int -> (Answer, Int)
solve (Q axioms fds rqs ops (gvs0, gkvs0) tvs0 uniformVariables hypotheses conclusions) z =
    trace "BEGIN" $
    traceInput (intercalate ", " tracedConclusions ++
                (if null hypotheses then "" else " if " ++ intercalate ", " tracedHypotheses) ++
                "?") $
    trace ("Uniform variables: " ++ intercalate ", " [ppx v | Kinded v _ <- uniformVariables]) $
    answerFrom (runTactic (init >> go) s0)

    where initialAssumptions = [(i, \pid -> PAssump pid id, p) | (i, (id, p)) <- zip [0..] hypotheses]

          -- Generic variables are those the solver is not allowed to improve.  This definition
          -- ensures that the solver is able to improve variables determined in the initial query,
          -- but not otherwise (even if they could be determined by possible solutions of the
          -- initial query).
          genericVariables required = vars conclusions \\ determined
              where determined = concatMap determinedFrom (required ++ map snd (hypotheses ++ conclusions))
                    determinedFrom p@(Pred cl _ _ _) = concat [vars (p `atDetermined` fd) | fd <- classFDs]
                        where classFDs = fromMaybe [] (lookup cl fds)

          tracedVariablesSubst = S ks ([v :-> TyVar (Kinded (Ident ("u_" ++ s) n f) k) | v@(Kinded (Ident s n f) k) <- uniformVariables] ++
                                       [v :-> TyVar (Kinded (Ident ("g_" ++ s) n f) k) | v@(Kinded (Ident s n f) k) <- gvs0])
              where S ks _ = empty

          tracedHypotheses = map ppx (tracedVariablesSubst ## map snd hypotheses)
          tracedConclusions = map ppx (tracedVariablesSubst ## map snd conclusions)


          -- Initial solver state: contains the goals and initial assumptions.  Everything else is
          -- introduced in the course of 'go'
          s0 = St { here = Cursor (Forest [] gs) g,
                    _trail = Trail { substitution = empty,
                                     assumptions = initialAssumptions,
                                     _requirements = [],
                                     ignored = Set.empty,
                                     invalid = Set.empty },
                    assumptionDependencies = [],
                    gvars0 = [],
                    gvars = [],
                    gkvars = gkvs0,
                    ovars_ = [],
                    uvars = uniformVariables,
                    next = z,
                    time = length hypotheses + 1,
                    nodeCount = length conclusions }
              where g:gs = [Tree n (emptyMetadata (-1)) | n <- [Goal name goal True Nothing | (name, goal) <- conclusions]]

          init = do addOpaque (ovars ops (hypotheses ++ conclusions) \\ tvs0)
                    rqs <- requirementTemplates
                    require Nothing rqs
                    trace (unlines ("Initial assumptions:" : ["    [" ++ show i ++ "] " ++ ppx p | (i, _, p) <- initialAssumptions])) (return ())
                    required <- fromRequirements [] initialAssumptions rqs
                    (impr, necessary) <- necessaryFromAssumptions axioms fds ops ([(pr, p) | (_, pr, p) <- initialAssumptions] ++ required)
                    let gvs' = genericVariables (impr ## (map snd (required ++ necessary)))
                        allAssumptions = map snd hypotheses ++ map snd required ++ map snd necessary
                    addAssumptions necessary
                    trace ("Generic variables: " ++ intercalate ", " [ppx v | Kinded v _ <- gvs' ++ gvs0]) (return ())
                    addInitialGeneric gvs0
                    addGeneric gvs'
                    -- pairwiseImprovement expects assumption indices in its arguments; however,
                    -- because the initial assumptions cannot be retracted later, we can afford to
                    -- pass dummy values (0s).
                    pairwiseImprs <- mapM (\((p, _), ps) -> pairwiseImprovement fds p ps)
                                          (split (zip (map (impr ##) allAssumptions) (repeat 0)))
                    let impr' = fromMaybe empty (concatSubsts (impr : map fst (concat pairwiseImprs)))
                    axImprs <- axImprLoop (impr' ## allAssumptions)
                    let impr'' = case axImprs of
                                   Nothing -> empty
                                   Just axImpr -> axImpr `compose` impr'
                    bindIrreversible impr''
                    mapM_ (try . assumptionImprovementByOracles) (map (impr'' ##) allAssumptions)

              where requirementTemplates = mapM inst rqs
                        where inst rq = do (_, Requires ps qs) <- instantiate ops rq
                                           return ([], ps, \prs -> [(q, \pid -> PRequired pid rid prs) | (rid, q) <- qs])

                    fromRequirements added [] _ = return added
                    fromRequirements added ((i, pr, p):assumed) rqs =
                        do (newRqs, newAssumptions) <- partitionEithers `fmap` sequence [ applyRequirement ops pr p rq `orElse` return (Left []) | rq <- rqs]
                           let newRqs' = concat newRqs
                               newAssumptions' = concat newAssumptions
                           is <- addAssumptions newAssumptions'
                           require (Just i) newRqs'
                           fromRequirements (newAssumptions' ++ added) (assumed ++ [(i, pr, p) | (i, (pr, p)) <- zip is newAssumptions']) (rqs ++ newRqs')

                    addAssumptions [] = return []
                    addAssumptions qs =
                        Tactic (\st -> let qs' = filterDuplicates qs st
                                       in trace ("Adding assumptions: " ++ intercalate ", " (map (ppx . snd) qs')) $
                                              (Progress [time st .. time st + length qs' - 1],
                                               st { _trail = (_trail st) { assumptions = [(i, pr, p) | (i, (pr, p)) <- zip [time st ..] qs'] ++ assumptions (_trail st) }
                                                  , time = time st + length qs' }))
                        where filterDuplicates qs st = filter (\(pr, q) -> let sq = s ## q in all (\(_, _, q') -> sq /= s ## q') (assumptions (_trail st))) qs
                                  where s = substitution (_trail st)

                    split [] = []
                    split [p] = []
                    split (p:ps) = (p,ps) : split ps

                    axImprLoop assumptions =
                        do imprs <- mapM (improvementFromAxioms axioms fds ops) assumptions
                           case concatSubsts imprs of
                             Nothing -> return Nothing
                             Just impr | isEmpty impr -> return (Just empty)
                                       | otherwise -> do impr' <- axImprLoop (impr ## assumptions)
                                                         return ((`compose` impr) `fmap` impr')

          go | null conclusions = exit (Done False)
             | otherwise        = do cs <- trail assumptionsConflict
                                     if not (null cs)
                                     then traceInput ("-- Proved ex falso! Conflicting assumptions:\n" ++ unlines ["-- " ++ ppx p ++ " and " ++ ppx q | (p, q) <- cs]) $
                                          exit (Done True)
                                     else whileProgressing (try (expand axioms fds ops) >> advance fds ops)

             where assumptionsConflict tr = return (filter (uncurry (conflicts fds)) (pairs [p | (_, _, p) <- assumptions tr]))
                   pairs []     = []
                   pairs (x:xs) = [(x, x') | x' <- xs] ++ pairs xs

          answerFrom (Exit reason, st)
              | null conclusions = (AnsProved [] (untag (substitution (_trail st))) False (nodeCount st), next st)
              | otherwise = (answer reason, next st)
              where answer (Done False) = AnsProved { evidence    = proofs
                                                    , improvement = untag (substitution (_trail st))
                                                    , exFalso     = False
                                                    , nodes       = nodeCount st }
                        where (proofs, [], _) = concatEntrails (map (entrails . nodeFrom) (ascend (here st)))
                    answer (Done True) = AnsProved { evidence    = [ (pid, PExFalso) | pid <- pids ]
                                                   , improvement = untag (substitution (_trail st))
                                                   , exFalso     = True
                                                   , nodes       = nodeCount st }
                        where pids = [ name | Tree (Goal name _ _ _) _ <- ascend (here st) ]
                    answer CantProgress = AnsStuck { evidence    = proofs
                                                   , remaining   = remaining
                                                   , improvement = impr
                                                   , nodes       = nodeCount st }
                        where (proofs, remaining, entrailsImpr) = concatEntrails (map (entrails . nodeFrom) (ascend (here st)))
                              impr = case concatSubsts [s, entrailsImpr] of
                                       Nothing -> s
                                       Just s' -> s'
                                  where s = untag (substitution (_trail st))
                    answer Failed = AnsFailed { contradicted = p, nodes = nodeCount st }
                        where Cursor _ t = here st
                              Just p     = contradiction (nodeFrom t)

                    concatEntrails es = (concat evss, concat remainings, fromMaybe empty (concatSubsts imprs))
                        where (_, evss, remainings, imprs) = unzip4 (map fromJust es)

                    ascend (Cursor (Forest left right) here) =
                        reverse left ++ here : right
                    ascend (Cursor (NodeP node left up right meta) here) =
                        ascend (Cursor up (Tree (withChildren node (reverse left ++ here : right)) meta))


                    -- The entrails of a node are (p, evs, remaining, impr) where:
                    --   p          is the proof being constructed at this node
                    --   evs        is any proofs constructed below the current node
                    --   remaining  is the goals remaining to be proved in this node
                    --   subst      is the improvement required at this node.

                    entrails :: Node -> Maybe (Proof, [(PId, Proof)], [(PId, Pred)], Subst)
                    entrails (Goal id p _ Nothing) = Just (PAssump id id, [], [(id, p)], empty)
                    entrails (Goal id p _ (Just t)) =
                        case entrails (nodeFrom t) of
                          Nothing -> Just (PAssump id id, [], [(id, p)], empty)
                          Just (pr, evs, remaining, impr) -> Just (pr, (id, pr) : evs, remaining, impr)
                    entrails (Clause name goal spin axid typs conditions (Right subtrees))
                        | null conditions || any (\(_, cond, _) -> isEmpty cond) conditions =
                            let clauseImprs = [impr | (_, cond, impr) <- conditions, isEmpty cond] in
                            do (prs, evs, remaining, imprs) <- unzip4 `fmap` mapM (entrails . nodeFrom) subtrees
                               return (PClause name axid typs prs, concat evs, concat remaining, fromMaybe empty (concatSubsts (imprs ++ clauseImprs)))
                        | otherwise = Nothing
                    entrails (Computed {}) = Nothing
                    entrails (Chain passed current remaining) =
                        do current' <- clauseFrom current
                           remaining' <- mapM clauseFrom remaining
                           if all (skipped . nodeFrom) passed &&
                              any (\c -> spin c == Disproving && either null null (subtrees c)) remaining' &&
                              all (\c -> spin c == Disproving) remaining'
                           then entrails current'
                           else Nothing
                        where clauseFrom (Tree c@(Clause {}) _) = Just c
                              clauseFrom (Tree (Stuck t) _)     = clauseFrom t
                              clauseFrom _                      = Nothing

                              skipped (Complete { proof = PInapplicable }) = True
                              skipped (Complete { proof = PSkip _ _ })     = True
                              skipped _                                    = False
                    entrails (Complete name _ Proving [] pr) = Just (pr, [(name, pr)], [], empty)
                    entrails (Exhausted t) = entrails (nodeFrom t)
                    entrails (Stuck t) = entrails (nodeFrom t)
                    entrails t = Nothing

                    contradiction (Goal _ _ _ Nothing)                       = Nothing
                    contradiction (Goal _ _ _ (Just t))                      = contradiction (nodeFrom t)
                    contradiction (Chain _ current _)                        = contradiction (nodeFrom current)
                    contradiction (Clause { subtrees = Right subtrees })     = msum (map (contradiction . nodeFrom) subtrees)
                    contradiction (Clause { subtrees = Left _ })             = Nothing
                    contradiction (Computed _ _ _ _ _ (Right subtrees))      = msum (map (contradiction . nodeFrom) subtrees)
                    contradiction (Computed _ _ _ _ _ (Left _))              = Nothing
                    contradiction (Alternatives as)                          = msum (map (contradiction . nodeFrom) as)
                    contradiction (Complete name goal Disproving [] _)       = Just (name, goal)
                    contradiction (Exhausted {})                             = Nothing
                    contradiction (Stuck t)                                  = contradiction (nodeFrom t)

solveAnonymous :: Query Pred -> Int -> (Answer, Int)
solveAnonymous (Q axioms fds rqs ops gvs0 tvs0 uniformVariables hypotheses conclusions) =
    solve (Q axioms fds rqs ops gvs0 tvs0 uniformVariables (zip hnames hypotheses) (zip cnames conclusions))
    where hnames = [toId ['$', chr i] | i <- [ord 'a' ..]]
          cnames = [toId ['$', chr i] | i <- [ord 'a' + length hypotheses..]]

run :: (Int -> (Answer, Int)) -> Answer
run f = fst (f 1)

----------------------------------------------------------------------------------------------------
