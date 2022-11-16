{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverloadedStrings, PatternGuards #-}
module Solver.Tactics where

import qualified Control.Applicative
import Control.Monad (MonadPlus(..), foldM, liftM2, msum, replicateM, when)
import qualified Control.Monad.Fail as Fail
import qualified Data.IntSet as Set
import Data.List
import Data.Maybe
import Data.Monoid(Monoid(..))
import Solver.PP
import Solver.Subst
import Solver.Syntax
import Solver.Trace

----------------------------------------------------------------------------------------------------
-- Habit Predicate Solver
----------------------------------------------------------------------------------------------------

-- This version begins laying the groundwork for improving the treatment of assumptions: we keep a
-- single set of assumptions (both assumed predicates and unifications), generalize the handling of
-- introducing and invalidating assumptions, and theoretically improve the performance of
-- invalidating assumptions by avoiding having to pack up and restore the entire solver state.

-- In broad outline: the solver state will consist of a forest storing the current states of the
-- proofs and a "trail" that stores the current set of assumptions, and a "time stamp" that
-- represents the number of introduced assumptions.  Unlike Prolog implementations, the trail is not a stack:
-- we'll be able to invalidate assumptions introduced further back without (necessarily)
-- invalidating assumptions introduced after them.  Each node in a tree represents either a goal
-- to solve, the progress towards solving a goal, or one of three possible
-- outcomes of attempting to solve a goal:
--
--   * A subtree can be stuck, meaning that it contains goals that have no applicable axioms; future
--     assumptions may allow us to refine the goal and find applicable axioms.
--
--   * Alternatively, a subtree may be exhausted (i.e., there are no remaining clauses to consider
--     because any matching clauses have been disproved). There is no way for future
--     assumptions to revive an exhausted subtree.
--
--   * Finally, a subtree may have been fully proved or disproved, in which case it can be
--     collapsed by combining the proofs.
--
-- We can regard the set of goals along the leaves of the forest as the "frontier" of the proof
-- search.  The solver operates in a breadth-first fashion over the frontier, replacing goals with
-- solving or stuck nodes and collapsing subtrees when they can no longer progress.

-- Next, we'll define the data structures that make up the solver trees and cursors over it.  We'll
-- define the trail and common operations with it.  We'll define a type for "tactics"; that is,
-- solver operations.  Tactics are monadic in structure, with some additional non-proper morphisms
-- for capturing progress and error/completion conditions.  Finally, we can define the top-level
-- solver and then define the major tactics that implement moving over the frontier, attempting to
-- solve single goals, and collapsing subgoals.

-- Nothing in this file invalidates the deduction algorithm published in ICFP 2010; however, we
-- elaborate it in several ways:

-- * The published algorithm regards proving a predicate and proving its opposite as
--   distinct operations; however, to avoid an exponential explosion of proofs, when we attempt to
--   solve a predicate we will simultaneously search for a proof and a counterproof.

-- * The published algorithm does not describe the process of computing improving subsitutions;
--   having to do so introduces much of the complexity of backtracking.

-- * [Oracles, proof by cases, etc.]

-- * Finally, we add some minor features, such as solving multiple goals in parallel and using
--   existing goals as assumptions when proving their siblings; these latter features are necessary
--   for the Habit implementation, even if they do not fundamentally extend the ilab system.


----------------------------------------------------------------------------------------------------
-- Solver Forest
----------------------------------------------------------------------------------------------------

-- A solver tree captures the state an individual proof.  For each node, we also track whether it
-- introduced assumptions, whether the last action that transformed it relied on any assumptions,
-- and the last time we looked at it.  These metadata are used to properly implement assumptions.
-- When a node is backtracked (either because it is disproved or because its children are
-- disproved), we invalidate any assumptions it introduced; if a node relied on any assumptions and
-- those assumptions are invalidated, we revert the node to the state before its last
-- transformation.  Finally, we use the last updated date to determine whether there's any chance
-- of recovering a stuck node: if no assumptions have been introduced since the node was originally
-- stuck, it can't be unstuck.

type TrailRef = Int
type RefSet   = Set.IntSet

data Metadata = Meta { lastUpdated       :: TrailRef
                     , introduces        :: RefSet
                     , childrenIntroduce :: RefSet
                     , dependsOn         :: RefSet
                     , history           :: [Tree] }
                deriving Show

emptyMetadata n = Meta { lastUpdated       = n
                       , introduces        = Set.empty
                       , childrenIntroduce = Set.empty
                       , dependsOn         = Set.empty
                       , history           = [] }

-- On to a tree itself.  Each node in the tree is also associated with a chunk of metadata:

data Tree = Tree { nodeFrom :: Node
                 , metaFrom :: Metadata }
            deriving Show

data Node = Goal { name     :: PId
                 , goal     :: Pred
                 , isRoot   :: Bool
                 , solution :: Maybe Tree }

          -- Clause, Chain, Computed, Cases, Alternatives cover the different
          -- types of tree nodes that represent in progress proofs.

          | Clause { name        :: PId
                   , goal        :: Pred
                   , spin        :: Spin
                   , axiomName   :: AxId
                   , typeArgs    :: [Type]
                   , conditions  :: [([TyId], Subst, Subst)]
                   , subtrees    :: Either [Pred] [Tree] }

          | Chain { passed    :: [Tree]     -- in practice, expect all these trees to be Completed (either skips or intersecting cases)
                  , current   :: Tree       -- in practice, expect this tree to be a Clause
                  , remaining :: [Tree] }   -- in practice, expect all these trees to be Clauses

          | Computed { name     :: PId      -- (Computed is for proofs using an oracle)
                     , goal     :: Pred
                     , spin     :: Spin
                     , inputs   :: [TyId]
                     , pbuilder :: [Proof] -> Tactic ()
                     , subtrees :: Either [Pred] [Tree] }

          | Alternatives { alternatives :: [Tree] }

          --

          | Complete { name        :: PId
                     , goal        :: Pred
                     , spin        :: Spin
                     , conditions  :: [([TyId], Subst, Subst)]
                     , proof       :: Proof }

          | Exhausted { subtree :: Tree }

          | Stuck { subtree :: Tree }

            deriving (Show)

instance Show ([Proof] -> Tactic ())
    where show _ = "<proof-builder>"

children :: Node -> [Tree]
children (Goal _ _ _ t)    = maybe [] (:[]) t
children n@(Clause {})     = either (const []) id (subtrees n)
children n@(Computed {})   = either (const []) id (subtrees n)
children (Chain _ t _)     = [t]
children (Alternatives as) = as
children (Complete {})     = []
children (Exhausted t)     = [t]
children (Stuck t)         = [t]

withChildren :: Node -> [Tree] -> Node
withChildren (Goal name goal isRoot _) [t] =
    Goal name goal isRoot (Just t)
withChildren (Clause name goal spin axid typs cond _) ts =
    Clause name goal spin axid typs cond (Right ts)
withChildren (Computed name goal spin vs pbuilder _) ts =
    Computed name goal spin vs pbuilder (Right ts)
withChildren (Chain skipped _ remaining) [t] =
    Chain skipped t remaining
withChildren (Alternatives _) ts =
    Alternatives ts
withChildren n@(Complete {}) _ =
    n
withChildren (Exhausted _) [t] =
    Exhausted t
withChildren (Stuck _) [t] =
    Stuck t

showConditionsShort [] = ""
showConditionsShort [(tyids, cond, _)] = " if (" ++ ppx tyids ++ ") " ++  ppx cond
showConditionsShort ((tyids, first, _) : rest) = " if (" ++ ppx tyids ++ ") " ++ ppx first ++ concat [" or " ++ ppx cond | (_, cond, _) <- rest]

showShort                                         :: Node -> String
showShort (Goal name goal isRoot Nothing)          = concat [if isRoot then "Root goal: " else "Goal: ", ppx name, ": ", ppx goal]
showShort (Goal name goal isRoot (Just _))         = concat ["Solving: ", ppx name, ": ", ppx goal, if isRoot then " at root" else ""]
showShort (Clause _ _ _ axid ts conditions _)      = concat ["Clause: ", ppx axid, "{", intercalate ", " (map ppx ts), "}", showConditionsShort conditions]
showShort (Computed {})                            = "Computed"
showShort (Chain _ current _)                      = concat ["Chain, at: ", showShort (nodeFrom current)]
showShort (Alternatives ts)                        = concat ["Alternatives: ", intercalate "; " (map (showShort . nodeFrom) ts)]
showShort (Complete name goal Proving conds pr)    = concat ["Proved (", showProofCtor pr, "): ", ppx name, ": " , ppx goal, showConditionsShort conds]
showShort (Complete name goal Disproving conds pr) = concat ["Disproved (", showProofCtor pr,  "): ", ppx name, ": ", ppx goal, showConditionsShort conds]
showShort (Exhausted t)                            = concat ["Exhausted: ", showShort (nodeFrom t)]
showShort (Stuck t)                                = concat ["Stuck: ", showShort (nodeFrom t)]

showProofCtor                 :: Proof -> String
showProofCtor PAx{}            = "PAx"
showProofCtor PCases{}         = "PCases"
showProofCtor PComputedCases{} = "PComputedCases"
showProofCtor PAssump{}        = "PAssump"
showProofCtor PRequired{}      = "PRequired"
showProofCtor PClause{}        = "PClause"
showProofCtor PSkip{}          = "PSkip"
showProofCtor PExFalso         = "PExFalse"
showProofCtor PInapplicable    = "PInapplicable"

-- Predicates over trees; the main purpose here is to distinguish the states that can make progress
-- (Goal and Solving) from those that cannot (Complete, Exhausted, Stuck).  We also distinguish the
-- two possible spins for complete nodes.

isProved, isDisproved, isExhausted, isStuck, isSolving :: Node -> Bool

isProved (Complete { spin = Proving })       = True
isProved _                                = False

isDisproved (Complete { spin = Disproving }) = True
isDisproved _                             = False

isExhausted (Exhausted _)                 = True
isExhausted _                             = False

isStuck (Stuck _)                         = True
isStuck _                                 = False

-- This assumes that stuck-ness has bubbled up the tree properly--that is, for example, that we
-- never see a Solving node in which the subtree is stuck without a Stuck node around the Solving
-- node as well.
isSolving Goal{}         = True
isSolving Clause{}       = True
isSolving Chain{}        = True
isSolving Alternatives{} = True
isSolving _              = False

----------------------------------------------------------------------------------------------------
-- Cursors and zippers

-- We adopt Huet's zipper technique to store locations within the forest: a cursor to a particular
-- node in the forest stores the subtree at that node and an "unzipped" path to the forest root.

data Path = Forest [Tree] [Tree]
          | NodeP Node [Tree] Path [Tree] Metadata
            deriving Show

data Cursor = Cursor Path Tree
              deriving Show

-- We'll only manipulate the cursor through tactics, so we define the zipper operations as tactics
-- rather than over the zipper itself.  (The Tactic type will be defined later on.)  The basic
-- operations are cursor transformations (such as movement up, down, left or right), querying the
-- current node, or replacing the current tree with a new one.

-- Cursor transformation.  While the argument is almost a tactic, note that it doesn't actually have
-- access to the solver state; this excludes oddities like moving the cursor during a cursor
-- transformation.
cursor :: (Cursor -> TacticResult Cursor) -> Tactic ()
cursor f = Tactic (\st -> case f (here st) of
                            Progress here' -> (Progress (), st { here = here' })
                            NoProgress -> (NoProgress, st)
                            Exit r -> (Exit r, st))

-- Apply tactic to the current tree.
tree :: (Tree -> Tactic t) -> Tactic t
tree f = Tactic (\st -> let Cursor _ t = here st in runTactic (f t) st)

-- Apply tactic to the current node.
node :: (Node -> Tactic t) -> Tactic t
node f = tree (f . nodeFrom)

meta :: (Metadata -> Tactic t) -> Tactic t
meta f = tree (f . metaFrom)

-- Updates the current node, preserving metadata.
update :: Node -> Tactic ()
update n = Tactic (\st -> let Cursor p t@(Tree _ meta) = here st
                              meta' = meta { lastUpdated = time st, history = t : history meta }
                          in (Progress (), st { here = Cursor p (Tree n meta') }))

dependOn :: RefSet -> Tactic ()
dependOn refs = tree depend'
    where depend' (Tree node meta) =
              if Set.null refs'
              then return ()
              else replaceT (Tree node meta { dependsOn = Set.union refs (dependsOn meta) })
              where refs' = refs Set.\\ dependsOn meta

-- Replaces the current node, resetting metadata.
replace :: Node -> Tactic ()
replace n = Tactic (\st -> let Cursor p _ = here st in (Progress (), st { here = Cursor p (Tree n (emptyMetadata (time st))) }))

replaceT :: Tree -> Tactic ()
replaceT t = Tactic (\st -> let Cursor p _ = here st in (Progress (), st { here = Cursor p t }))

-- Constructs new trees
new :: Node -> Tactic Tree
new n = Tactic (\st -> (Progress (Tree n (emptyMetadata (time st))), st { nodeCount = nodeCount st + 1 }))

-- Cursor movement can be defined using the 'cursor' function above; these functions are all fairly
-- simple manipulations.  Note that we represent inability to move as a failure to progress, not as
-- an error.

up, down, left, right :: Tactic ()

up = depart >> cursor up' >> arrive
    where up' (Cursor (NodeP node left up right meta) here) =
              Progress (Cursor up (Tree (withChildren node (reverse left ++ here : right)) meta))
          up' _ = NoProgress

down = cursor down' >> arrive
    where down' (Cursor up (Tree node meta)) =
              case children node of
                [] -> NoProgress
                (t:ts) -> Progress (Cursor (NodeP node [] up ts meta) t)

left = depart >> cursor left' >> arrive
    where left' (Cursor (Forest (l:left) right) here) =
              Progress (Cursor (Forest left (here:right)) l)
          left' (Cursor (NodeP node (l:left) up right meta) here) =
              Progress (Cursor (NodeP node left up (here:right) meta) l)
          left' _ = NoProgress

right = depart >> cursor right' >> arrive
    where right' (Cursor (Forest left (r:right)) here) =
              Progress (Cursor (Forest (here:left) right) r)
          right' (Cursor (NodeP node left up (r:right) meta) here) =
              Progress (Cursor (NodeP node (here:left) up right meta) r)
          right' _ = NoProgress

----------------------------------------------------------------------------------------------------
-- Displaying the forest
----------------------------------------------------------------------------------------------------

-- prefixChildren takes a list of comments (i.e., clauses remaining in a chain or stored conditions
-- and improvements) and a list of printed children, and produces a tree including the comments and
-- linking to each of the children.
prefixChildren :: [String] -> [[String]] -> [String]
prefixChildren cs [] = cs
prefixChildren cs sss = (map ("|" ++) cs) ++ ["|"] ++ concat (intersperse ["|"] (reverse (go (reverse sss))))
    where go (ss:sss) = final ss : map norm sss
          norm (s:ss) = ("+" ++ s) : map ("|" ++) ss
          final (s:ss) = ("\\" ++ s) : map (" " ++) ss

-- Generate a string for each node.  There are some points here that could reasonably be controlled
-- by options or similar: whether the remaining nodes in chains are displayed; whether stored
-- conditions and improvements are displayed; and, whether proofs are displayed.
nodeString :: Node -> [String]
nodeString (Goal name goal _ _) = [ppx name ++ ": " ++ ppx goal ++ "?"]
nodeString (Clause _ _ spin axid typeArgs conditions subgoals) = [ppx spin ++ " by " ++ ppx axid ++ typeArgsString] ++
                                                                 conditionString ++ subgoalsString
    where typeArgsString | null typeArgs = ""
                         | otherwise = "[" ++ intercalate ", " (map ppx typeArgs) ++ "]"
          conditionString = [" [ if (" ++ ppx tyids ++ ") " ++ ppx cond ++ (if isEmpty impr then "" else ", implying " ++ ppx impr) | (tyids, cond, impr) <- conditions]
          subgoalsString = case subgoals of
                             Left [] -> []
                             Left ps -> [" { " ++ intercalate ", " (map ppx ps)]
                             Right _ -> [] -- will be displayed as subtrees
nodeString (Chain skipped current remaining) = ["Chain"] ++ subgoalsString
    where subgoalsString = concat [(" { " ++ s) : map ("   " ++) ss | (s:ss) <- map (printNode . nodeFrom) remaining]
nodeString (Computed _ _ spin inputs _ subgoals) = ["Oracle " ++ ppx spin ++ " based on " ++ intercalate ", " (map ppx inputs)] ++ subgoalsString
    where subgoalsString = case subgoals of
                             Left ps -> [" { " ++ intercalate ", " (map ppx ps)]
                             Right _ -> [] -- will be displayed as subtrees
nodeString (Alternatives _) = ["Either of"]
nodeString (Complete name goal spin conditions (PSkip _ (n, pr))) = ["Skip, disproved hypothesis " ++ show n, "    by " ++ ppx pr]
nodeString (Complete name goal spin conditions proof) = [resultString ++ ppx name ++ ": " ++ ppx goal] ++ proofString ++ conditionString
    where resultString = case spin of
                           Proving -> "Proved "
                           Disproving -> "Disproved "
          proofString = ["    by " ++ ppx proof]
          conditionString = [" [ if (" ++ ppx tyids ++ ") " ++ ppx cond ++ (if isEmpty impr then "" else ", implying " ++ ppx impr) | (tyids, cond, impr) <- conditions]
nodeString (Exhausted _) = ["Exhausted"]
nodeString (Stuck _) = ["Stuck"]

printNode :: Node -> [String]
printNode (Stuck t) = ("(Stuck) " ++ nString) : prefixChildren nComments (map printTree (children (nodeFrom t)))
    where nString : nComments = nodeString (nodeFrom t)
printNode n = nString : prefixChildren nComments (map printTree (children n))
    where nString : nComments = nodeString n

printTree :: Tree -> [String]
printTree t = ("--" ++ s) : map ("  " ++) ss
    where (s:ss) = printNode (nodeFrom t)

printPath :: [String] -> Path -> [String]
printPath here (Forest left right) = prefixChildren [] (map printTree left ++ [here] ++ map printTree right)
printPath here (NodeP orig left up right _) = printPath (("--" ++ origString) : map ("  " ++) (prefixChildren origComments (map printTree left ++ [here] ++ map printTree right))) up
    where origString : origComments = nodeString orig

printCursor :: Cursor -> String
printCursor (Cursor up here) = unlines (printPath (pointer (printTree here)) up)
    where pointer ((_ : _ : s) : ss) = (">>" ++ s) : ss


-- explain s t runs tactic t; if it makes progress, explain traces the given string and the forest
-- (after the tactic completes).
explain :: String -> Tactic a -> Tactic a
explain s t =
    do v <- t
       Tactic (\st -> trace (s ++ "\n" ++ printCursor (here st)) (Progress v, st))

explainHeader :: String -> Tactic a -> Tactic a
explainHeader s = explain ("-- " ++ s ++ ' ' : replicate (80 - length s - 4) '-')

checkDepth :: Tactic ()
checkDepth =
    do n <- depth
       s <- Tactic (\st -> (Progress (printCursor (here st)), st))
       check checkSolverTreeDepth (< n) ("Maximum tree depth exceeded.\n" ++ s) (return ())

    where depth = Tactic (\st -> let Cursor p _ = here st in (Progress (up p), st))
          up Forest{} = 0
          up (NodeP _ _ p _ _) = 1 + up p

----------------------------------------------------------------------------------------------------
-- Solver Trail
----------------------------------------------------------------------------------------------------

-- The trail captures the (indexed) assumptions made in the proof so far; we use the indices to
-- identify particular assumptions in the trail.  Along with the assumptions themselves, we also
-- store a list of (indices to) assumptions that should not be used in the current context; this
-- represents (for instance) the assumptions introduced by the parents of the current node.

data Trail = Trail { substitution       :: TaggedSubst
                   , assumptions        :: [PredAssumption]
                   , _requirements      :: [(Maybe Int, RequirementTemplate)]
                   , ignored            :: RefSet
                   , invalid            :: [PredAssumption] }
             deriving Show
type PredAssumption = (TrailRef, PCon, Pred)
     -- when assumption introducted, function for constructing proof from name, assumed pred,

instance Show ([Proof] -> [(Pred, PCon)])
    where show _ = "<rqt>"

instance Show PCon
    where show f = "<pcon>"

-- Lifting trail transformers to tactics (with optional return value)

trail_ :: (Trail -> TacticResult (r, Trail)) -> Tactic r
trail_ f = Tactic (\st -> case f (_trail st) of
                            Progress (r, trail') -> (Progress r, st { _trail = trail' })
                            NoProgress           -> (NoProgress, st)
                            Exit r               -> (Exit r, st))

trail :: (Trail -> Tactic t) -> Tactic t
trail f = trail_ (\t -> Progress (t, t)) >>= f

-- Primitive trail tactics.  As with the primitive cursor manipulation functions above, these do not
-- attempt to keep the solver state consistent; for instance, removing an assumption does not affect
-- nodes that relied on it.

startIgnoring :: RefSet -> Tactic ()
startIgnoring ids | Set.null ids = return ()
                  | otherwise    = trail_ (\tr -> Progress ((), tr { ignored = Set.union ids (ignored tr) }))

stopIgnoring :: RefSet -> Tactic ()
stopIgnoring ids | Set.null ids = return ()
                 | otherwise    = trail_ (\tr -> Progress ((), tr { ignored = ignored tr Set.\\ ids }))

depart = meta (stopIgnoring . introduces)

arrive = do checkValid
            updateIntroducedAssumptions
            updateChildAssumptions
            meta (startIgnoring . introduces)

checkValid = Tactic check >>= invalidateAssumptions

    where findValid invalidated t@(Tree _ meta)
              | Set.null (Set.intersection invalidated (dependsOn meta)) = t
              | otherwise = findValid invalidated (head (history meta))

          check st | Set.null (Set.intersection inv (dependsOn meta)) = (Progress Set.empty, st)
                   | otherwise = (Progress newlyInvalid, st { here = Cursor up t' })
              where Cursor up t@(Tree _ meta) = here st
                    inv = Set.fromList [i | (i, _, _) <- invalid (_trail st)]
                    t'@(Tree _ meta') = findValid inv t
                    newlyInvalid = childrenIntroduce meta Set.\\ childrenIntroduce meta'

-- This makes me sad
invalidAssumptions :: Tactic [PId]
invalidAssumptions = trail invalids
    where invalids t = let pids = concatMap getAssumptionPId (invalid t) in
                       trace (unlines [ "Invalid assumptions: " ++ ppx pids]) $
                       return pids

          getAssumptionPId (_, pcon, _) =
              case pcon "_" of
                PAssump _ pid -> [pid]
                p             -> trace ("Unable to extract PId from " ++ ppx p) []

updateChildAssumptions :: Tactic ()
updateChildAssumptions = Tactic update'
    where update' st = ( Progress ()
                       , st { here = Cursor up (Tree node (meta { childrenIntroduce = newChildAssumptions })) })
              where Cursor up (Tree node meta) = here st
                    newChildAssumptions =
                        case node of
                          Complete {} -> childrenIntroduce meta -- no children, but we still need to track the assumptions used
                          _           -> let metadata = map metaFrom (children node)
                                         in Set.unions (map introduces metadata ++ map childrenIntroduce metadata)

updateIntroducedAssumptions :: Tactic ()
updateIntroducedAssumptions = Tactic update'
    where update' st = (Progress (),
                        st { here = Cursor up (Tree node meta { introduces = introduces' }),
                             assumptionDependencies = remaining })
              where Cursor up (Tree node meta) = here st
                    (introduces', remaining) = splitDependencies (introduces meta) (assumptionDependencies st)
                    splitDependencies is pairs  -- compute transitive closure of dependencies on assumptions introduced by current node
                        | null pairs' = (is, pairs)
                        | otherwise   = splitDependencies (Set.union (Set.fromList (map snd pairs')) is) pairs''
                        where (pairs', pairs'') = partition ((`Set.member` is) . fst) pairs

checkTrail st =
    check checkTrailLength
          (< (length assumed + length binds))
          ("Maximum trail length exceeded.\nForest:\n" ++ printCursor (here st) ++ "\nTrail:\n" ++ shownAssumps ++ "\n" ++ shownSubst)
    where binds        = let TS _ bs = substitution (_trail st) in bs
          assumed      = assumptions (_trail st)
          shownAssumps = intercalate "\n" ["[" ++ show i ++ "] " ++ ppx p | (i, _, p) <- assumed]
          shownSubst   = intercalate "\n" [ppx v ++ " -> " ++ ppx t | (_, v :-> t) <- binds]


-- bindGeneral (and special cases bind, bindIrreversible) update the trail to account for a new substitution:

bindGeneral :: Bool -> Subst -> Tactic [TrailRef]
bindGeneral irreversible s
    | isEmpty s = return []
    | otherwise = trail (\tr -> case s `under` substitution tr of
                                  Left err -> trace ("Rejected attempt to bind " ++ ppx s ++ ": " ++ err)
                                              noProgress
                                  Right s' -> do (is, as) <- Tactic (bind' s')
                                                 when (not (null as)) $
                                                     trace ("Invalidating duplicated assumptions: " ++ ppx (Set.fromList as)) $
                                                     invalidateAssumptions (Set.fromList as)
                                                 return is)

    where bind' (S ks bs) st =
              checkTrail st $
              traceIf (not (null newUVars)) ("Adding new uniform variables: " ++ intercalate ", " (map ppx newUVars)) $
              trace ("Attempting to bind " ++ ppx s') $
              (Progress (is, duplicates (reverse (assumptions (_trail st)))),
               st{ here = Cursor up (Tree node (meta{ lastUpdated = time st
                                                    , introduces = if irreversible
                                                                   then introduces meta
                                                                   else Set.union (Set.fromList is) (introduces meta) }))
                 , _trail = (_trail st) { substitution = s'' }
                 , gvars = filterGenerics (gvars st)
                 , uvars = newUVars ++ uvars st
                 , time  = time st + length bs })

              where Cursor up (Tree node meta) = here st
                    is = take (length bs) [time st..]
                    s' = TS ks (zip is bs)
                    s'' = compose (substitution (_trail st)) s'


                    duplicates :: [PredAssumption] -> [TrailRef]
                    duplicates as = iter [] as
                        where iter _ [] = []
                              iter ps ((i, pr, p):as)
                                  | p' `elem` ps = i : iter ps as
                                  | otherwise = iter (p' : ps) as
                                  where p' = s'' ## p

                    -- see motivating example in tests/solver/tests/generic2:
                    filterGenerics gvs = filter (`notElem` newlyDetermined) gvs
                        where newlyDetermined = vars [t | (v :-> t) <- bs, v `notElem` gvs]

                    newUVars = vars [t | (v :-> t) <- bs, v `elem` uvars st]

bind, bindIrreversible :: Subst -> Tactic [TrailRef]
bind                    = bindGeneral False
bindIrreversible        = bindGeneral True

-- Add a predicate assumption to the trail:

addToTrail :: Pred -> PCon -> Tactic Int
addToTrail p pr = Tactic add
    where add st = checkTrail st $
                   trace ("Assuming " ++ ppx p ++ " as [" ++ show i ++ "] " ++ ppx pr) $
                   ( Progress i
                   , st { here = Cursor up (Tree node (meta { lastUpdated = i
                                                            , introduces = Set.insert i (introduces meta) }))
                        , _trail = (_trail st) { assumptions = (i, pr, p) : assumptions (_trail st) }
                        , time = i + 1 })
              where Cursor up (Tree node meta) = here st
                    i = time st

-- Retrieve all current Requirement Templates (ignoring ones that depend on parents of the current node)

requirements :: Tactic [RequirementTemplate]
requirements = trail (\tr -> return [ rqt | (i, rqt) <- _requirements tr, notExcluded i (ignored tr)])
    where notExcluded Nothing _   = True
          notExcluded (Just i) is = not (i `Set.member` is)

-- Add a requirement (template) to the trail:

require :: Maybe TrailRef -> [RequirementTemplate] -> Tactic ()
require _ [] = return ()
require i rs = trace ("Adding requirement for: [" ++ show i ++ "] " ++
                              intercalate "; " [ "{" ++ intercalate ", " (map ppx ids) ++ "} " ++ intercalate ", " (map ppx ps) | (ids, ps, _) <- rs]) $
                       trail_ (\tr -> Progress ((), tr { _requirements = [(i, r) | r <- rs] ++ _requirements tr }))

-- Misc. tactics:

addInitialGeneric :: [TyId] -> Tactic ()
addInitialGeneric vs = Tactic (\st -> (Progress (), st { gvars0 = vs ++ gvars0 st }))

addGeneric :: [TyId] -> Tactic ()
addGeneric vs = Tactic (\st -> (Progress (), st { gvars = vs ++ gvars st }))

generics :: Tactic ([TyId], [Id]) -- (generic type vars, generic kind vars)
generics = Tactic (\st -> (Progress (gvars st ++ gvars0 st, gkvars st), st))

addOpaque :: [TyId] -> Tactic ()
addOpaque vs = Tactic (\st -> (Progress (), st { ovars_ = vs ++ ovars_ st }))

opaqueVariables :: Tactic [TyId]
opaqueVariables = Tactic (\st -> (Progress (ovars_ st), st))

wrap, wrapGeneric :: (([TyId], [Id]) -> t -> t -> UnificationResult) -> t -> t -> Tactic Subst
wrap              = wrap' ([], [])
wrapGeneric f x y = do gens <- generics; wrap' gens f x y
wrap' gens f x y  = case f gens x y of
                      Left _ -> noProgress
                      Right s -> return s

matches, matchesGeneric, matchesInfinitary, unifies, unifiesGeneric, unifiesUniform :: Unifies t => t -> t -> Tactic Subst
matches            = wrap match
matchesGeneric     = wrapGeneric match
matchesInfinitary  = wrap matchInfinitary
unifies            = wrap unify
unifiesGeneric     = wrapGeneric unify
unifiesUniform x y = Tactic (\st -> case unify (gvars st ++ gvars0 st ++ uvars st, gkvars st) x y of
                                      Left _ -> (NoProgress, st)
                                      Right s -> (Progress s, st))

-- guardAxiomApplication succeeds iff we have not previously applied axioms to the given predicate.
guardAxiomApplication :: FunDeps -> Pred -> Tactic ()
guardAxiomApplication fds p@(Pred cl ts _ _) = trail f
    where f tr = do parentGoals <- getParentGoals
                    seenAlready <- mapM (matchesP . (substitution tr ##)) parentGoals
                    case catMaybes seenAlready of
                      [] -> trace (ppx p ++ " does not match any of " ++ intercalate ", " (map (ppx . (substitution tr ##)) parentGoals) ++ " under any of " ++ intercalate ", " (map show classFDs)) $
                            return ()
                      (p':_) -> trace ("Blocking axiom application to " ++ ppx p ++ " as we are attempting to prove " ++ ppx p') noProgress
          matchesP p' = msum `fmap` mapM (\fd -> conditional ((matchesInfinitary `modFD` fd) p p') (const (return (Just p'))) (return Nothing)) classFDs
          classFDs = fromMaybe [[0..length ts - 1] :~> []] Nothing -- (lookup cl fds)

          getParentGoals = Tactic (\st -> let Cursor up _ = here st in (Progress (climb up), st))

          climb (Forest _ _) = []
          climb (NodeP (Goal { goal = p }) _ up _ _) = p : climb up
          climb (NodeP _ _ up _ _) = climb up


----------------------------------------------------------------------------------------------------
-- Tactics
----------------------------------------------------------------------------------------------------

data Tactic t = Tactic { runTactic :: SolverState -> (TacticResult t, SolverState) }

-- Progress is the successful result for a tactic; NoProgress is the unsuccessful result.
-- NoProgress behaves like a recoverable error case.  The Exit case terminates the solver.

data TacticResult t = Progress t
                    | NoProgress
                    | Exit Reason
                      deriving Show

data Reason = Done Bool       -- a Boolean True indicates that the assumptions were false (ExFalso)
            | CantProgress
            | Failed
              deriving Show

instance Functor TacticResult
    where fmap f (Progress t) = Progress (f t)
          fmap _ NoProgress   = NoProgress
          fmap _ (Exit r)     = Exit r

data SolverState = St { here      :: Cursor
                      , _trail    :: Trail
                      , assumptionDependencies :: [(TrailRef, TrailRef)]
                      , gvars0    :: [TyId]     -- caller specified list of variables that must be treated as generic
                      , gvars     :: [TyId]     -- solver inferred list of generic variables
                      , gkvars    :: [Id]       -- generic kind variables (from caller)
                      , ovars_    :: [TyId]     -- opaque variables (appear only in opaque positions, computed by solver)
                      , uvars     :: [TyId]     -- uniform variables (vars that can be improved, but not by cases)
                      , next      :: Int        -- used for fresh name generation
                      , time      :: TrailRef   -- current time, monotonic
                      , nodeCount :: !Int }     -- total number of nodes created (for profiling/curiousity)
                   deriving Show

instance Functor Tactic
    where fmap f t = Tactic (\st -> case runTactic t st of
                                      (Progress r, st') -> (Progress (f r), st')
                                      (NoProgress, _)   -> (NoProgress, st)
                                      (Exit r, st')     -> (Exit r, st'))

instance Applicative Tactic
    where pure r = Tactic (\st -> (Progress r, st))
          (<*>)  = liftM2 ($)

instance Control.Applicative.Alternative Tactic
    where empty = mzero
          (<|>) = mplus

instance Monad Tactic
    where 
          t >>= f  = Tactic (\st -> case runTactic t st of
                                      (Progress r, st') -> runTactic (f r) st'
                                      (NoProgress, _)   -> (NoProgress, st)
                                      (Exit r, st')     -> (Exit r, st'))

-- We treat fail as being equivalent to NoProgress; this means throwing away the error string that's
-- provided with fail.  If we were generating some kind of trace, it might be valuable to keep those
-- strings to provide diagnostic information on why tactics are being skipped, but at the moment I
-- don't think it would serve any purpose.

instance Fail.MonadFail Tactic
    where fail _   = Tactic (\st -> (NoProgress, st))

-- return, noProgress, and exit correspond to the three constructors of the TacticResult type.

instance MonadPlus Tactic
    where mzero = Tactic (\st -> (NoProgress, st))
          t0 `mplus` t1 = conditional t0 return t1

noProgress :: Tactic t
noProgress = mzero

exit :: Reason -> Tactic t
exit r = Tactic (\st -> (Exit r, st))

-- try and orElse manage failure to progress: try t always succeeds, regardless of t, and t0 `orElse`
-- t1 succeeds if either succeeds.  whileProgressing provides a basic looping construct.

try :: Tactic t -> Tactic ()
try t = (t >> return ()) `orElse` return ()

infixr 1 `orElse`
orElse :: Tactic a -> Tactic a -> Tactic a
orElse = mplus

-- whileProgressing always succeeds, even if the first attempt to use t fails.
whileProgressing :: Tactic t -> Tactic ()
whileProgressing t = (t >> whileProgressing t) `orElse` return ()

conditional :: Tactic t -> (t -> Tactic u) -> Tactic u -> Tactic u
conditional condition consequent alternative =
    Tactic (\st -> case runTactic condition st of
                     (Progress r, st') -> runTactic (consequent r) st'
                     (NoProgress, _)   -> runTactic alternative st
                     (Exit r, st')     -> (Exit r, st'))

anyOf :: [Tactic t] -> Tactic t
anyOf = foldr orElse noProgress

-- tick and now provide a notion of time, corresponding to the number of assumptions introduced.

tick, now :: Tactic Int
tick = Tactic (\st -> let x = time st in (Progress x, st { time = x + 1 }))
now  = Tactic (\st -> (Progress (time st), st))

fresh :: Id -> Tactic Id
fresh (Ident s _ f) = Tactic (\st -> let x = next st
                                     in (Progress (Ident s x f), st { next = x + 1 }))

instantiate :: HasVars t => Opacities -> Scheme t -> Tactic ([Type], t)
instantiate ops (Forall ks x) =
    do vs <- replicateM (length ks) (fresh "t")
       let ts = [TyVar (Kinded v k) | (v, k) <- zip vs ks]
           x' = inst ts x
       addOpaque (ovars ops x')
       return (ts, inst ts x)

instantiateAxiom :: Opacities -> Axiom -> Tactic (Name, [([Type], QPred)])
instantiateAxiom ops (Ax name chain) =
    do chain' <- mapM (instantiate ops) chain
       return (name, chain')

-- 'assumptionDepends a b' means that assumption 'a' depends on assumption 'b'

assumptionDepends :: TrailRef -> TrailRef -> Tactic ()
assumptionDepends a b = Tactic (\st -> (Progress (), st { assumptionDependencies = (a, b) : assumptionDependencies st }))

----------------------------------------------------------------------------------------------------
-- Using the Trail
----------------------------------------------------------------------------------------------------

-- At this point, we can define the two high-level operations that make use of the trail.
-- applyTrail attempts to apply the trail to the current goal, first by applying the current
-- substitution and then by checking the resulting goal against the assumptions, looking for either
-- an assumption of the goal, an assumption that contradicts the goal, or an assumption that induces
-- an improvement.  invalidate is the opposite: it invalidates any assumptions introduced by the
-- current node (regardless of node type), and invalidates and reverts any nodes that relied on
-- those assumptions.  invalidate is recursive: it invalidates all children of the current node, in
-- addition to the nodes that depend on the current node.  It does not, however, revert the current
-- node.


----------------------------------------------------------------------------------------------------
-- applyTrail
--

pairwiseImprovement :: FunDeps -> Pred -> [(Pred, TrailRef)] -> Tactic [(Subst, TrailRef)]
pairwiseImprovement _ _ [] = return []
pairwiseImprovement fds p@(Pred className _ _ _) qs
    | null classFDs = return []
    | otherwise     = trace ("Computing pairwise improvement from " ++ ppx p ++ " and " ++ ppx (map fst qs)) $
                      do mss <- sequence `fmap` mapM improvementFrom qs
                         case mss of
                           Just ss -> let ss' = filter (not . isEmpty . fst) ss
                                      in if allConsistent (map fst ss')
                                         then return ss'
                                         else return []
                           _       -> return []

              where classFDs = fromMaybe [] (lookup className fds)

                    improvementFrom :: (Pred, TrailRef) -> Tactic (Maybe (Subst, TrailRef))
                    improvementFrom (q@(Pred className' _ _ _), aid)
                        | className /= className' = return (Just (empty, aid))
                        | otherwise = do ss <- mapM try classFDs
                                         return (do s <- concatSubsts =<< sequence ss
                                                    return (s, aid))
                        where try fd | ((==) `atDetermining` fd) p q = (Just `fmap` (unifiesGeneric `atDetermined` fd) q p)
                                                                       `orElse` return Nothing
                                     | otherwise                     = return (Just empty)

                    allConsistent substs = and [ consistent s s' | (s:ss) <- tails substs, s' <- ss ]

applyTrail :: FunDeps -> Tactic ()
applyTrail fds = explainHeader "applyTrail" $
                 tryAll [applyCurrentSubstitution, improvePairwise, solveByAssumptions]
    where tryAll ts = do bs <- mapM succeeds ts
                         if or bs then return () else noProgress
              where succeeds  :: (Node -> Trail -> Tactic r) -> Tactic Bool
                    succeeds f = (nodeAndTrail f >> return True) `orElse` return False

                    nodeAndTrail  :: (Node -> Trail -> Tactic r) -> Tactic r
                    nodeAndTrail f = Tactic (\st -> let Cursor _ tree = here st
                                                    in runTactic (f (nodeFrom tree) (_trail st)) st)

          -- Test to see if there are any improvements that refine this goal, in which case we
          -- can update the goal and record the associated set of dependencies.
          applyCurrentSubstitution :: Node -> Trail -> Tactic ()
          applyCurrentSubstitution (Goal name p isRoot subtree) tr
              | p /= p'   = trace ("Improved goal " ++ ppx name ++ ": " ++ ppx p ++ " to " ++ ppx p') $
                            do update (Goal name p' isRoot subtree)
                               dependOn is
              | otherwise = noProgress
              where W p' is = substitution tr # p
          applyCurrentSubstitution _ _ = noProgress

          -- Attempt pairwise improvement between the current goal and other assumptions.
          improvePairwise :: Node -> Trail -> Tactic ()
          improvePairwise (Goal name p@(Pred className _ _ _) isRoot Nothing) tr =
              do substs <- pairwiseImprovement fds p as
                 (p', is) <- foldM bindImprovement (p, []) substs
                 when (not (null is)) $
                     trace ("Improved goal " ++ ppx name ++ ": " ++ ppx p ++ " to " ++ ppx p') $
                     do update (Goal name p' isRoot Nothing)
                        dependOn (Set.fromList is)
              where as = [(substitution tr ## q, i) | (i, pr, q@(Pred className' _ _ _)) <- assumptions tr,
                                                      className == className']
                    bindImprovement (p, is) (s, aid) =
                        do is' <- bind s
                           mapM_ (`assumptionDepends` aid) is'
                           return (if p /= p' then (p', is' ++ is) else (p, is))
                        where p' = s ## p
          improvePairwise _ _ = noProgress

          --
          solveByAssumptions :: Node -> Trail -> Tactic ()
          solveByAssumptions (Goal name p@(Pred className _ _ _) isRoot child) tr =
              case child of
                Nothing -> do discharging <- catMaybes `fmap` mapM (relevant p) as
                              case discharging of
                                ((spin, pr, is) : _) -> let prf = pr name in
                                                        do invalid <- invalidAssumptions
                                                           if any (`elem` invalid) (assumptionsIn prf)
                                                           then noProgress
                                                           else trace ("Solved " ++ ppx name ++ ": " ++ ppx p ++ " by " ++ ppx is ++ " " ++ ppx pr) $
                                                                do update (Complete name p spin [] (pr name))
                                                                   dependOn is
                                _                   -> noProgress

                {- Apply non-circular assumptions to goals after initial exploration.

                   This is the immediate payoff for dynamic backtracking.  Previously, the
                   solver was occasionally dependent on the order in which it encountered
                   predicates.  For example, consider the following ilab example:

                   > Eq t u | t ~> u, u ~> t.
                   > Eq t t.
                   >
                   > C t if D t.
                   >
                   > C t, Eq t u if C u?

                   In this case, when the solver initially encounters the goal 'C t', it
                   has no suitable assumption to discharge the goal, and so applies the
                   axiom 'C t if D t', leaving the goal 'D t'.  The solver can then prove
                   the goal 'Eq t u', introducing the improving substitution [t/u].
                   However, this does not, by itself, prove 'D u', and backtracking to
                   before the expansion of 'C t' would also backtrack over the computation
                   of the improving substitution.

                   With dynamic backtracking, however, we are able to observe that the
                   binding [t/u] does not depend on any assumptions resulting from the
                   assumption of 'C t', and so it safe to backtrack those assumptions and
                   solve the goal using the assumption 'C u' and the improving
                   substitution.
                -}
                Just _  -> do introduced <- meta (\m -> return (Set.union (introduces m) (childrenIntroduce m)))
                              -- trim substitution to remove bindings that depend on the current node (avoid cycles)
                              let s' = TS ks (filter (\(i, _) -> not (i `Set.member` introduced)) binds)
                                  W p' is' = s' # p
                              trace ("Rechecking assumptions for " ++ ppx name ++ ": " ++ ppx p' ++ " (introduces " ++ ppx introduced ++ ")") (return ())
                              discharging <- catMaybes `fmap` mapM (relevant p') as
                              -- trim predicate assumptions that depend on the current node (avoid cycles)
                              let discharging' = filter (\(_, _, is) -> Set.null (Set.intersection is introduced)) discharging
                              case discharging' of
                                ((spin, pr, is) : _) -> let prf = pr name in
                                                        do invalid <- invalidAssumptions
                                                           if any (`elem` invalid) (assumptionsIn prf)
                                                           then noProgress
                                                           else trace ("Solved " ++ ppx name ++ ": " ++ ppx p ++ " by " ++ ppx is ++ " " ++ ppx pr) $
                                                                do meta (invalidateAssumptions . childrenIntroduce)
                                                                   update (Complete name p spin [] prf)
                                                                   dependOn (Set.union is is')
                                _ -> noProgress

              where s@(TS ks binds) = substitution tr
                    as = [(q', pr, Set.insert i is)
                              | (i, pr, q@(Pred className' _ _ _)) <- assumptions tr,
                                className == className',
                                not (i `Set.member` ignored tr),
                                let W q' is = s # q]
                    classFDs = fromMaybe [] (lookup className fds)

                    -- Test if a given predicate can be proved or disproved from an assumption.
                    relevant :: Pred -> (Pred, PCon, RefSet) -> Tactic (Maybe (Spin, PCon, RefSet))
                    relevant p (q, pr, is)
                        | proving p q = return (Just (Proving, pr, is))
                        | otherwise = do b <- disproving p q
                                         if b then return (Just (Disproving, pr, is))
                                         else return Nothing
                        where -- Test to see if the first predicate is proved by the second, either because they
                              -- are equal, or else as a result of a functional dependency.
                              proving    :: Pred -> Pred -> Bool
                              proving p q = p == q || any provingUnder classFDs  -- does q prove p?
                                  where provingUnder fd = flag p == Exc && flag q == Inc &&
                                                          ((==) `atDetermining` fd) p (invert q) &&
                                                          ((/=) `atDetermined` fd) p (invert q)

                              -- Test to see if the first predicate is disproved by the second
                              disproving    :: Pred -> Pred -> Tactic Bool
                              disproving p q | p == invert q = return True
                                             | otherwise     = or `fmap` mapM disprovingUnder classFDs
                                  where disprovingUnder fd
                                            | flag p == Inc && flag q == Inc && ((==) `atDetermining` fd) p q =
                                                conditional ((unifiesGeneric `atDetermined` fd) p q)
                                                            (const (return False))
                                                            (return True)
                                            | otherwise = return False
          solveByAssumptions _ _ = noProgress

----------------------------------------------------------------------------------------------------
-- invalidate

invalidateAssumptions :: RefSet -> Tactic ()
invalidateAssumptions is
    | Set.null is = return ()
    | otherwise   = trace ("Invalidating assumptions: " ++ showSet is) $
                    Tactic (\st -> let tr          = _trail st
                                       valid i     = not (i `Set.member` is)
                                       TS ks binds = substitution tr
                                       (newAssumptions, invalidAssumptions) =
                                           partition (\(i, _, _) -> valid i) (assumptions tr)
                                   in  (Progress (),
                                        st{ _trail = tr{ invalid       = invalidAssumptions ++ invalid tr,
                                                         assumptions   = newAssumptions,
                                                         substitution  = TS ks (filter (\(i, _) -> valid i) binds),
                                                         _requirements = filter (\(mi, _) -> maybe True valid mi) (_requirements tr) },
                                            assumptionDependencies = [(i, i') | (i, i') <- assumptionDependencies st, valid i, valid i'] }))

invalidate :: Tactic ()
invalidate = meta (invalidateAssumptions . childrenIntroduce)
