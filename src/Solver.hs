{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances, OverloadedStrings, ScopedTypeVariables #-}
module Solver (module Solver, module S) where

import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import qualified Solver.Subst as S
import Solver.Tactics as Solver hiding (improvement, remaining)
import Solver.Main as Solver hiding (run)
import Solver.PP as Solver
import Solver.Syntax as S
import Solver.Validation as V
import Solver.Cycles
import Solver.Trace

import Printer.Common ((<::>))
import Printer.XMPEG
import Syntax.IMPEG as I
import Syntax.IMPEG.TSubst
import qualified Syntax.IMPEG.KSubst as K
import Syntax.XMPEG as X

internal s = error ("Internal: Solver interface: " ++ s)

type SolverEnv = (Axioms, FunDeps, Requirements, RequirementImpls, Opacities)

convertSnd (x, y) = (x, convert y)

----------------------------------------------------------------------------------------------------

type IQP              = I.Qual (I.PredType I.Pred KId) (I.PredType I.Pred KId)
type IPred            = Located (I.PredType I.Pred KId)
type IType            = I.Type KId

instance Convertable AxId Id
    where convert (AxId id Nothing)  = id
          convert (AxId id (Just i)) = fromString (fromId id ++ '_' : show i)

instance Convertable IType S.Type
    where convert (I.TyCon tyid)               = S.TyCon tyid
          convert (I.TyVar tyid)               = S.TyVar tyid
          convert (I.TyGen {})                 = internal "I.TyGen"
          convert (I.TyApp (At _ t) (At _ t')) = convert t :@ convert t'
          convert (I.TyNat i)                  = S.TyLit i
          convert (I.TyKinded (At _ t) _)      = convert t
          convert (I.TyLabel (Ident name n f)) = S.TyCon (Kinded (Ident ("$Label" ++ name) n f) KLabel)

instance Convertable S.Type IType
    where convert (S.TyCon tyid@(Kinded (Ident name n f) _))
              | take 6 name == "$Label" = I.TyLabel (Ident (drop 6 name) n f)
              | otherwise               = I.TyCon tyid
          convert (S.TyVar tyid)        = I.TyVar tyid
          convert (S.TyGen _)           = internal "S.TyGen"
          convert (t S.:@ t')           = I.TyApp (introduced (convert t)) (introduced (convert t'))
          convert (S.TyLit i)           = I.TyNat i

instance Convertable I.Flag S.Flag
    where convert Holds = Inc
          convert Fails = Exc

instance Convertable S.Flag I.Flag
    where convert Inc = Holds
          convert Exc = Fails

instance Convertable IPred S.Pred
    where convert (At pos (I.Pred className ts flag)) =
              S.Pred className (map (convert . dislocate) ts) (convert flag) pos

instance Convertable S.Pred IPred
    where convert (S.Pred className ts flag pos) =
              At pos (I.Pred className (map (introduced . convert) ts) (convert flag))

instance Convertable IQP S.QPred
    where convert (ps I.:=> p) =
              map convert ps S.:=> convert p

instance Convertable S.QPred IQP
    where convert (ps S.:=> p) = map convert ps I.:=> convert p

instance Convertable IQP (S.Scheme S.QPred)
    where convert qp = S.Forall ks (S.gen 0 vs qp')
              where qp' = convert qp
                    vs  = S.vars qp'
                    ks  = map kind vs

instance Convertable (S.Scheme S.QPred) IQP
    where convert (S.Forall ks qp) = convert (S.inst ts qp)
              where names = [name | Kinded name _ <- S.vars qp]
                    vs = filter (`notElem` names) [fromString ("t" ++ show i) | i <- [0..]]
                    ts = map S.TyVar (zipWith Kinded vs ks)

instance Convertable (I.Fundep Int) (S.FunDep)
    where convert (xs I.:~> ys) = xs S.:~> ys

----------------------------------------------------------------------------------------------------

instance Convertable X.Type S.Type
    where convert (X.TyCon kid)    = S.TyCon kid
          convert (X.TyVar kid)    = S.TyVar kid
          convert (X.TyGen i)      = internal "I.TyGen"
          convert (X.TyApp t t')   = convert t :@ convert t'
          convert (X.TyNat i)      = S.TyLit i
          convert (X.TyLabel (Ident name n f)) = S.TyCon (Kinded (Ident ("$Label" ++ name) n f) KLabel)

instance Convertable S.Type X.Type
    where convert (S.TyCon tyid@(Kinded (Ident name n f) _))
              | take 6 name == "$Label" = X.TyLabel (Ident (drop 6 name) n f)
              | otherwise               = X.TyCon tyid
          convert (S.TyVar tyid)        = X.TyVar tyid
          convert (S.TyGen _)           = internal "S.TyGen"
          convert (t S.:@ t')           = X.TyApp (convert t) (convert t')
          convert (S.TyLit i)           = X.TyNat i

instance Convertable (X.Pred X.Type) S.Pred
    where convert (X.Pred name ts f) = S.Pred name (map convert ts) (convert f) introducedLocation

instance Convertable S.Pred (X.Pred X.Type)
    where convert (S.Pred name ts f _) = X.Pred name (map convert ts) (convert f)

instance Convertable S.ProofPattern X.EvPat
    where convert (S.Pat axid ts pvars) = X.EvPat (convert axid) (map convert ts) pvars

instance Convertable S.RqImpl ([X.EvPat], X.Ev)
    where convert (pats, pr) = (convert pats, fromMaybe (error "Solver.hs:119") (lookup "$impl" evs))
              where binds :: [ConditionalBindings X.Type]
                    (evs, binds) = disentangleProofs [("$impl", pr)]

----------------------------------------------------------------------------------------------------
-- Specific types avoid ambiguities introduced by empty lists in type inference, and I think that
-- (for the moment, anyway) type inference is the only place that should be building solver
-- environments.

mergeRqImpls :: S.RqImpls -> X.RequirementImpls -> X.RequirementImpls
mergeRqImpls newImpls implMap = foldr insert implMap [(rqid, impl) | (rqid, impls) <- newImpls', impl <- impls]
    where RqImpls newImpls' = newImpls
          insert (rqid, impl) implMap = trace ("Adding requirement implementation: " ++ show (ppr impl')) $
                                        Map.insertWith (\_ impls -> impl' : impls) rqid [impl'] implMap
              where impl' = convert impl

newAxioms :: [(Id, [IQP], Bool)] -> SolverEnv -> Either String (([[IQP]], [String]), SolverEnv)
newAxioms newAxs (axs, fds, rqs, rqm, ops) =
    case runV (addAxioms axs fds rqs ops newAxs') of
      Left err                              -> Left err
      Right ((newAxs'', axs', rqImpls), ws) -> Right ((reordered axIds newAxs'', ws), (axs', fds, rqs, mergeRqImpls rqImpls rqm, ops))
    where axIds   = [id | (id, _, _) <- newAxs]
          newAxs' = [(S.Ax (UserSupplied name) (map convert qps), gfp) | (name, qps, gfp) <- newAxs]
          reordered [] _ = []
          reordered (id:ids) newAxs = find newAxs : reordered ids newAxs
              where find (Ax (UserSupplied id') qps : rest)
                        | id == id' = map convert qps
                        | otherwise = find rest
                    find _ = error ("Solver.hs:156:Axiom " ++ show (ppr id) ++ " went missing.")

newFunDep :: Id -> I.Fundep Int -> SolverEnv -> Either String ((), SolverEnv)
newFunDep className fd (axs, fds, rqs, rqm, ops) = Right ((), (axs, fds', rqs, rqm, ops))
    where fd' = convert fd
          fds' = mergeFDs [(className, [fd'])] fds

newRequirement :: [IPred] -> [(Id, IPred)] -> SolverEnv -> Either String ((), SolverEnv)
newRequirement ps qs (axs, fds, rqs, rqm, ops) =
    case runV_ (mergeRequirements fds rqs [rqScheme]) of
      (([], rqs'), []) -> Right ((), (axs, fds, rqs', rqm, ops))
      ((errs, _), []) -> Left (unlines errs)
    where rq = Requires (map convert ps) (map convertSnd qs)
          vs = S.vars rq
          rqScheme = S.Forall (map kind vs) (S.gen 0 vs rq)

newOpacity :: Id -> Int -> SolverEnv -> Either String ((), SolverEnv)
newOpacity className i (axs, fds, rqs, rqm, ops) = Right ((), (axs, fds, rqs, rqm, ops'))
    where ops' = mergeOpacities [(className, [i])] ops

----------------------------------------------------------------------------------------------------

type ConditionalBindings ty = Either [([(KId, ty)], [(KId, ty)])] ([KId], [KId], [ty] -> [ty])

entails :: (Convertable pred S.Pred, Convertable S.Pred pred, Convertable ty S.Type, Convertable S.Type ty,
            Convertable ty' S.Type, Convertable S.Type ty', Printable pred) =>
           SolverEnv -> ([KId], [Id]) -> [KId] -> [KId] -> [(Id, pred)] -> [(Id, pred)] -> Int ->
           Either pred (EvSubst, [(Id, pred)], K.KSubst, [(Kinded Id, ty)], [ConditionalBindings ty'], Int)
entails env@(_, _, _, rqm, _) gvs0 tvs0 uniformVariables hypotheses conclusions z =
    case invokeSolver env gvs0 tvs0 uniformVariables hypotheses' conclusions' z of
      Left (_, spred) ->
          Left (convert spred)
      Right (proofs, unsolved, (ks, binds), z')
          | cyclic (map snd proofs) ->
              error (unlines ("Cyclic proofs" : ["    " ++ show (ppr v) ++ " +-> " ++ show (ppx p) | (v, p) <- proofs]))
          | otherwise ->
              let (proofs', conditionalBindings) = disentangleProofs proofs
              in case filter (`notElem` (map fst unsolved ++ map fst hypotheses)) (concatMap (evVars . snd) proofs') of
                   [] -> Right (proofs',
                                map convertSnd unsolved,
                                ks,
                                [(id, convert ty) | (id, ty) <- binds],
                                conditionalBindings,
                                z')
                   unbound -> error (unlines (["!! Failed in disentangle proofs! Unbound evidence variables " ++ intercalate ", " (map (show . ppr) unbound),
                                               "!! Hypotheses were:" ++ intercalate ", " (map (show . ppr . fst) hypotheses),
                                               "!! Input proofs were:"] ++
                                              map (ppx . snd) proofs ++
                                              ["!! And resulting evidence expressions were:"] ++
                                              [show (ppr v) ++ " = " ++ show (ppr p) | (v, p) <- proofs']))

    where hypotheses' = map convertSnd hypotheses
          conclusions' = map convertSnd conclusions

----------------------------------------------------------------------------------------------------

invokeSolver :: SolverEnv -> ([KId], [Id]) -> [KId] -> [KId] -> [(Id, S.Pred)] -> [(Id, S.Pred)] -> Int ->
                Either (Id, S.Pred) ([(Id, S.Proof)], [(Id, S.Pred)], (K.KSubst, [(Kinded Id, S.Type)]), Int)
invokeSolver (axs, fds, rqs, rqm, ops) gvs0 tvs0 uniformVariables hypotheses conclusions z =
    case solve (Q axs fds rqs ops gvs0 tvs0 uniformVariables hypotheses conclusions) z of
      (AnsProved evidence impr _ _, z') -> Right (evidence, [], pairsFrom impr, z')
      (AnsStuck evidence remaining impr _, z') -> Right (evidence, remaining, pairsFrom impr, z')
      (AnsFailed p _, _) -> Left p
    where pairsFrom (S.S ks binds) = (ks, [(name, ty) | (name S.:-> ty) <- binds])

----------------------------------------------------------------------------------------------------


disentangleProofs :: forall ty. (Convertable S.Type ty, Convertable ty S.Type) => [(Id, S.Proof)] -> (EvSubst, [ConditionalBindings ty])
disentangleProofs ps = let evs = [(v, fromMaybe (error "Solver.hs:133") (Map.lookup v evidence)) | v <- topLevel]
                       in trace (unlines ("Results:" : ["    " ++ show (ppr v) ++ "  ->  " ++ show (ppr e) | (v, e) <- evs])) (evs, cbinds)
    where topLevel = map fst ps
          (evidence, cbinds) = (Map.fromList (concat evPairs), concat cbindss)
              where (evPairs, cbindss) = unzip (map tlEvidence ps)

          lookupVariable v = fromMaybe (X.EvVar v) (Map.lookup v evidence)

          tlEvidence :: (Id, S.Proof) -> ([(Id, X.Ev)], [ConditionalBindings ty])
          tlEvidence (v, PAssump _ v') | v == v' = ([(v, X.EvVar v)], [])
          tlEvidence (v, p)                      = ((v, ev) : evs, cbinds)
              where (ev, cbinds, evs) = evidenceFrom p

          evidenceFrom :: S.Proof -> (X.Ev, [ConditionalBindings ty], [(Id, X.Ev)])
          evidenceFrom (PAssump pid aid)
              | pid == aid = (X.EvVar pid, [], [(pid, X.EvVar pid)])
              | otherwise = (p, [], [(pid, p)])
              where p = lookupVariable aid
          evidenceFrom (PAx id ax ts _ ps) = (ev, concat cbinds, (id, ev) : concat ss)
              where (evs, cbinds, ss) = unzip3 (map evidenceFrom ps)
                    ev = X.EvCons (X.Inst (convert ax) (map convert ts) evs)
          evidenceFrom (PClause id ax ts ps) = (ev, concat cbinds, concat ss)
              where (evs, cbinds, ss) = unzip3 (map evidenceFrom ps)
                    ev = X.EvCons (X.Inst (convert ax) (map convert ts) evs)
          evidenceFrom (PRequired pid rid ps) =
              (X.EvRequired rid evs, concat cbinds, (pid, X.EvRequired rid evs) : concat ss)
              where (evs, cbinds, ss) = unzip3 (map evidenceFrom ps)
          evidenceFrom (PCases id cs) = (X.EvCases cs', [Left cbinds], (id, X.EvCases cs') : concat ss)
              where (cs', cbinds, ss) = unzip3 (map evidenceFromCase cs)
                    evidenceFromCase (cond, impr, ev)
                        | not (null cbinds) = error "Solver.hs:232"  -- This seems to rule out nested conditional improvements---why?
                        | otherwise         = ((pairsFrom cond, ev'), (pairsFrom cond, pairsFrom impr), map addCase ss)
                        where pairsFrom (S.S ks binds) = [(name, convert ty) | (name S.:-> ty) <- binds]  -- TODO: safe to ignore kind substitution?
                              addCase (id, ev) = (id, X.EvCases [(pairsFrom cond, ev)])
                              (ev', cbinds, ss) = evidenceFrom ev
          evidenceFrom (PComputedCases id args results imprcon pcon) = (ev, [Right (args, results, imprcon')], [(id, ev)])
              where disentangle pr = fromMaybe (error "Solver.hs:234") (lookup id (fst (disentangleProofs [(id, pr)] :: (EvSubst, [ConditionalBindings ty]))))
                    ev = X.EvComputed args (disentangle . pcon . convert)
                    imprcon' :: [ty] -> [ty]
                    imprcon' ts = map convert (imprcon (convert ts))
          evidenceFrom (PFrom evpat p p') = (X.EvFrom evpat' ev ev', concat cbinds, map addFrom (concat ss))
              where evpat' = convert evpat
                    ([ev, ev'], cbinds, ss) = unzip3 (map evidenceFrom [p, p'])
                    addFrom (id, ev') = (id, X.EvFrom evpat' ev ev')
          evidenceFrom x = error (show x)
