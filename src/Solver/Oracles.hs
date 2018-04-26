{-# LANGUAGE OverloadedStrings #-}
module Solver.Oracles (assumptionImprovementByOracles, determinable, fundeps, primitiveClasses, solveByOracles)  where

import qualified Data.IntSet as Set
import Solver.PP
import Solver.Subst hiding (singleton)
import Solver.Syntax
import Solver.Tactics
import Syntax.Common (Fixity(..), Assoc(..))
import qualified Syntax.IMPEG.KSubst as K

import Solver.Trace

type Oracle = PId -> Pred -> Tactic (Subst, Tactic ())

singleton v t = S K.empty [v :-> t]

solved :: Spin -> Id -> Tactic ()
solved spin s = node solved'
    where solved' (Goal name goal _ Nothing) =
              trace ("Solved " ++ ppx name ++ ": " ++ ppx goal ++ " by oracle " ++ ppx s) $
              update (Complete name goal spin [] (PAx name (AxId s Nothing) [] [] []))
          solved' _ =
              noProgress

solvedByCases :: [TyId] -> [TyId] -> ([Type] -> [Type]) -> Id -> Tactic ()
solvedByCases args results impr s = node solved'
    where -- I think this Goal case should become unnecessary
          solved' (Goal name goal _ Nothing) = solve name goal
          solved' (Computed name goal spin _ _ _) = solve name goal
          solved' _ =
              noProgress

          checkUniform = Tactic (\st -> if any (`elem` uvars st) results then (NoProgress, st) else (Progress (), st))
          solve name goal =
              do checkUniform
                 trace ("Solved " ++ ppx name ++ ": " ++ ppx goal ++ " by cases, oracle " ++ ppx s)
                       (update (Complete name goal Proving []
                                         (PComputedCases name args results impr (\_ -> PAx name (AxId s Nothing) [] [] []))))

prove, disprove :: Id -> Tactic ()
prove    = solved Proving
disprove = solved Disproving

infixr 2 `xor`
True `xor` False = True
False `xor` True = True
_ `xor` _        = False

known :: (Pred -> Bool) -> Tactic Bool
known f = trail (\tr -> return (any (\(i, _, p) -> not (i `Set.member` ignored tr) && f (substitution tr ## p)) (assumptions tr)))

----------------------------------------------------------------------------------------------------

arithmetic :: Oracle
arithmetic name goal@(Pred className ts flag loc) =
    case (className, ts) of
      ("<",   [a, b])    -> lt a b
      ("+",   [a, b, c]) -> add a b c flag
      ("*",   [a, b, c]) -> mult a b c flag
      ("/",   [a, b, c]) -> div a b c flag
      ("^",   [a, b, c]) -> exp a b c flag
      ("GCD", [a, b, c]) -> gcdP a b c flag
      _                  -> noProgress
    where lt (TyLit i) (TyLit j)
              | i < j `xor` flag == Exc = return (empty, prove "Oracles_arithmetic_lt")
              | otherwise               = return (empty, disprove "Oracles_arithmetic_lt")
          lt (TyVar v) (TyLit c)        = do b <- known sumPred
                                             if b then return (empty, prove "Oracles_summand_less_than_sum")
                                                  else noProgress
              where sumPred (Pred "+" [t, t', TyLit c'] Inc _) =
                        (t == TyVar v && c' < c) || (t' == TyVar v && c' < c)
                    sumPred _ = False
          lt (TyLit 0) (TyVar v)        = do b <- known expPred
                                             if b then return (empty, prove "Oracles_zero_less_than_exp")
                                                  else noProgress
                where -- check for a predicate of the form x^y = v, having already
                      -- seen 0 < v.
                      expPred (Pred "^" [_, _, TyVar w] Inc _) = v==w
                      expPred _                                = False
          lt _ _                        = noProgress

          add (TyLit a) (TyLit b) (TyLit c) _
              | a + b == c `xor` flag == Exc = return (empty, prove "Oracles_arithmetic_add")
              | otherwise                    = return (empty, disprove "Oracles_arithmetic_add")
          add (TyVar s) (TyLit b) (TyLit c) Inc
              | c >= b    = return (singleton s (TyLit (c - b)), prove "Oracles_arithmetic_add")
              | otherwise = return (empty, disprove "Oracles_arithmetic_add")
          add (TyLit a) (TyVar s) (TyLit c) Inc
              | c >= a    = return (singleton s (TyLit (c - a)), prove "Oracles_arithmetic_add")
              | otherwise = return (empty, disprove "Oracles_arithmetic_add")
          add (TyLit a) (TyLit b) (TyVar s) Inc =
              return (singleton s (TyLit (a + b)), prove "Oracles_arithmetic_add")
          add (TyVar v) (TyVar w) (TyLit c) Inc =
              return (empty, do caseOnV <- caseOn v w c
                                caseOnW <- caseOn w v c
                                altNode <- new (Alternatives [caseOnV, caseOnW])
                                node (\g@(Goal {}) -> update g { solution = Just altNode }))
              where caseOn v w c =
                        new (Computed name goal Proving [v] (pbuilder v w c) (Left [Pred "<" [TyVar v, TyLit (c + 1)] Inc loc]))
                    pbuilder v w c _ = solvedByCases [v] [w] (\[TyLit nv] -> [TyLit (c - nv)]) "Oracles_arithmetic_add"
          add _ _ _ _ = noProgress

          mult (TyLit a) (TyLit b) (TyLit c) _
               | a * b == c `xor` flag == Exc = return (empty, prove "Oracles_arithmetic_mult")
               | otherwise                    = return (empty, disprove "Oracles_arithmetic_mult")
          mult (TyVar s) (TyLit b) (TyLit c) Inc
              | c == 0 && b /= 0 =
                  return (singleton s (TyLit 0), prove "Oracles_arithmetic_mult")
              | c == 0           =
                  noProgress
              | otherwise        =
                  case divMod c b of
                    (a, 0) -> return (singleton s (TyLit a), prove "Oracles_arithmetic_mult")
                    _      -> return (empty, disprove "Oracles_arithmetic_mult")
          mult (TyLit a) (TyVar s) (TyLit c) Inc
              | c == 0 && a /= 0 =
                  return (singleton s (TyLit 0), prove "Oracles_arithmetic_mult")
              | c == 0           =
                  noProgress
              | otherwise        =
                  case divMod c a of
                    (b, 0) -> return (singleton s (TyLit b), prove "Oracles_arithmetic_mult")
                    _      -> return (empty, disprove "Oracles_arithmetic_mult")
          mult (TyLit a) (TyLit b) (TyVar s) Inc =
              return (singleton s (TyLit (a * b)), prove "Oracles_arithmetic_mult")
          mult _ _ _ _ = noProgress

          div (TyLit a) (TyLit b) (TyLit c) flag
              | a `divMod` b == (c, 0) `xor` flag == Exc = return (empty, prove "Oracles_arithmetic_div")
              | otherwise                                = return (empty, disprove "Oracles_arithmetic_div")
          div (TyLit a) (TyLit b) (TyVar s) Inc =
              case a `divMod` b of
                (c, 0) -> return (singleton s (TyLit c), prove "Oracles_arithmetic_div")
                _      -> return (empty, disprove "Oracles_arithmetic_div")
          div (TyLit a) (TyVar s) (TyLit c) Inc =
              case a `divMod` c of
                (b, 0) -> return (singleton s (TyLit b), prove "Oracles_arithmetic_div")
                _      -> return (empty, disprove "Oracles_arithmetic_div")
          div (TyVar s) (TyLit b) (TyLit c) Inc =
              return (singleton s (TyLit (b * c)), prove "Oracles_arithmetic_div")
          div _ _ _ _ = noProgress

          exp (TyLit a) (TyLit b) (TyLit c) flag
              | a ^ b == c `xor` flag == Exc = return (empty, prove "Oracles_arithmetic_exp")
              | otherwise = return (empty, disprove "Oracles_arithmetic_exp")
          exp (TyLit a) (TyLit b) (TyVar s) Inc =
              return (singleton s (TyLit (a ^ b)), prove "Oracles_arithmetic_exp")
          exp (TyLit a) (TyVar s) (TyLit 1) flag
              | flag == Exc = return (empty, disprove "Oracles_arithmetic_exp")
              | otherwise   = return (singleton s (TyLit 0), prove "Oracles_arithmetic_exp")
          exp (TyLit a) (TyVar s) (TyLit c) flag =
              case repeatedDivide c a of
                Nothing | flag == Exc -> return (empty, prove "Oracles_arithmetic_exp")
                        | otherwise   -> return (empty, disprove "Oracles_arithmetic_exp")
                Just b  | flag == Exc -> return (empty, disprove "Oracles_arithmetic_exp")
                        | otherwise   -> return (singleton s (TyLit b), prove "Oracles_arithmetic_exp")
              where repeatedDivide c a
                        | c < a  = Nothing
                        | c == a = Just 1
                        | otherwise = case c `divMod` a of
                                        (b, 0) -> do n <- repeatedDivide b a
                                                     return (n + 1)
                                        _      -> Nothing
          exp (TyLit n) (TyVar v) (TyVar w) Inc =
              return (empty, solvedByCases [v] [w]
                                           (\[TyLit m] -> [TyLit (n ^ m)])
                                           "Oracles_arithmetic_exp")
          exp (TyVar v) (TyVar w) (TyVar x) Inc =
              return (empty, solvedByCases [v, w] [x]
                                           (\[TyLit m, TyLit n] -> [TyLit (m ^ n)])
                                           "Oracles_arithmetic_exp")
          exp _ _ _ _ = noProgress

          -- TODO: There's scope for more improvement here.  For example,
          --  GCD m m = n   ==>   m = n
          --  GCD 1 m = n   ==>   m = n
          --  GCD m 1 = n   ==>   m = n
          gcdP (TyLit 0) (TyLit 0) r _
              | flag == Exc             = return (empty, prove "Oracles_arithmetic_gcd")
              | otherwise               = return (empty, disprove "Oracles_arithmetic_gcd")
          gcdP (TyLit a) (TyLit b) (TyLit c) _
              | gcd a b == c `xor` flag == Exc = return (empty, prove "Oracles_arithmetic_gcd")
              | otherwise                      = return (empty, disprove "Oracles_arithmetic_gcd")
          gcdP (TyLit a) (TyLit b) (TyVar s) Inc
              = return (singleton s (TyLit (gcd a b)), prove "Oracles_arithmetic_gcd")
          gcdP _ _ _ _ = noProgress

----------------------------------------------------------------------------------------------------
-- TODO work on the matrix here
linearity :: Id -> Pred -> Tactic (Subst, Tactic ())
linearity name goal@(Pred className ts flag loc) =
    case (className, ts) of
      ("SeFun", [t]) -> sefun t
      ("ShFun", [t]) -> shfun t
      ("Un", [t]) -> un t
      -- ("->", [t]) -> un t
      _           -> noProgress

    where un ((TyVar v :@ _) :@ _) =
              do b <- known (funPred v)
                 if b
                 then return (singleton v (arrowLike "-!&>"), prove "Oracles_linearity_un")
                 else noProgress
          un (TyVar v) =
              do b <- known (funPred v)
                 if b
                 then return (singleton v (arrowLike "-!&>"), prove "Oracles_linearity_un")
                 else noProgress
          un _ = noProgress

          sefun (TyVar v) = do b <- known unPred
                               if b
                               then return (singleton v (arrowLike "-!*>"), prove "Oracles_linearity_fun")
                               else noProgress
              where unPred (Pred "Un" [TyVar w] Inc _)             = v == w
                    unPred (Pred "Un" [(TyVar w :@ _) :@ _] Inc _) = v == w
                    unPred _                                       = False
          sefun _ = noProgress

          shfun (TyVar v) = do b <- known unPred
                               if b
                               then return (singleton v (arrowLike "-!&>"), prove "Oracles_linearity_fun")
                               else noProgress
              where unPred (Pred "Un" [TyVar w] Inc _)             = v == w
                    unPred (Pred "Un" [(TyVar w :@ _) :@ _] Inc _) = v == w
                    unPred _                                       = False
          shfun _ = noProgress

          funPred v (Pred "->" [TyVar w] Inc _) = trace ("SOLVER DEBUG\n\t" ++ ppx v ++ " =?= " ++ ppx w ++ " = " ++ show (v == w)) $
                                                   v == w
          -- funPred v (Pred "SeFun" [TyVar w] Inc _) = trace ("SOLVER DEBUG\n\t" ++ ppx v ++ " (-*>) =?= " ++ ppx w ++ " = " ++ show (v == w)) $
          --                                         v == w
          -- funPred v (Pred "ShFun" [TyVar w] Inc _) = trace ("SOLVER DEBUG\n\t" ++ ppx v ++ " (-&>) =?= " ++ ppx w ++ " = " ++ show (v == w)) $
          --                                         v == w
          funPred _ _                             = False

          arrowLike id = TyCon (Kinded (Ident id 0 (Just (Fixity RightAssoc 5))) (KFun KStar (KFun KStar KStar)))

----------------------------------------------------------------------------------------------------

solveByOracles = node oracles'
    where oracles' (Goal name p _ Nothing) = do (impr, act) <- anyOf [arithmetic name p, linearity name p]
                                                bindGeneric impr
                                                act
          oracles' _                       = noProgress

          bindGeneric (S ks ps) = Tactic (\st -> if all (\(v :-> _) -> v `notElem` gvars st) ps
                                                 then runTactic (bind (S ks ps)) st
                                                 else trace ("Rejecting non-generic improving substitution: " ++ ppx (S ks ps)) $
                                                      (NoProgress, st))

assumptionImprovementByOracles p =
    do (impr, _) <- anyOf [arithmetic "_" p, linearity "_" p]
       trace ("From assumption " ++ ppx p ++ ", improving " ++ ppx impr) $
           bind impr

primitiveClasses :: [Id]
primitiveClasses = ["<", "+", "-", "*", "/", "GCD"]

fundeps :: FunDeps
fundeps = [ ("+", [[0, 1] :~> [2], [0, 2] :~> [1], [1, 2] :~> [0]])
          , ("*", [[0, 1] :~> [2]])
          , ("^", [[0, 1] :~> [2]])
          , ("GCD", [[0, 1] :~> [2]]) ]

determinable :: [(Id, [Integer])]
determinable = [ ("Un", [0]) ]
