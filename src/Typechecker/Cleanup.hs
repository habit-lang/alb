-- Purpose:
--
-- The type checker annotates the XMPEG programs that it generates with
-- ESubst nodes to capture delayed substitutions of value, evidence, and type
-- variables.  In principal, the type checker could apply these substitutions
-- as soon as they are known.  In practice, however, this could be expensive,
-- requiring multiple traversals of the source tree.  Instead, the code in
-- this file, designed to run after type checking is complete, will apply all
-- of the substitutions in a single pass over the source tree, producing an
-- output Program that does not contain any ESubst values.
--
-- Implementation:
--
-- The code is a straightforward walk over the abstract syntax of MPEG.  At
-- the top level, there are three separate substitution components for value,
-- evidence, and type variables, which are initially empty, but are extended
-- with new bindings at each ESubst node.  The substitutions are consulted
-- every time a variable of the appropriate kind is found to determine if a
-- substution should be made.
--

{-# LANGUAGE FlexibleInstances #-}
module Typechecker.Cleanup (cleanupProgram) where

import Common
import Data.Maybe
import Syntax.XMPEG
import Syntax.XMPEG.TSubst

cleanupProgram :: Pass st (Program KId) (Program KId)
cleanupProgram = return . cleanup [] [] []

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

class CleanType t
  where cleanType :: [KId] -> t -> t

instance CleanType Type
  where cleanType vs vt@(TyVar v@(Kinded _ k))
            | v `elem` vs = vt
            | otherwise = TyCon (Kinded "Zero" k)
        cleanType vs (TyApp t t') = TyApp (cleanType vs t) (cleanType vs t')
        cleanType _ t = t

instance CleanType (Pred Type)
  where cleanType vs (Pred cl ts f) = Pred cl (map (cleanType vs) ts) f

instance CleanType t => CleanType (Scheme t)
  where cleanType vs (Forall ws ps t) = Forall ws (map (cleanType vs) ps) (cleanType vs t)

cleanTypeBinding :: [KId] -> TypeBinding -> ([KId], TypeBinding)
cleanTypeBinding vs (Left bs) = (vs ++ concat wss, Left bs')
    where (wss, bs') = unzip (map cleanCase bs)
          cleanCase (cond, impr) = (map fst impr, (clean cond, clean impr))
              where clean bs = [(kid, cleanType vs ty) | (kid, ty) <- bs]
cleanTypeBinding vs (Right (ws, ws', f)) = (vs ++ ws', Right (ws, ws', map (cleanType vs) . f))


--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

class Cleanup e
  where cleanup :: [KId] -> ExprSubst -> EvSubst -> e -> e

instance Cleanup t => Cleanup [t]
  where cleanup vs exs evs = map (cleanup vs exs evs)

instance Cleanup t => Cleanup (Id, t)
  where cleanup vs exs evs (i, t) = (i, cleanup vs exs evs t)

instance Cleanup Expr
  where cleanup vs exs evs = c
          where
           c (ELamVar i)                = fromMaybe (ELamVar i) (cleanup vs exs evs `fmap` lookup i exs)
           c (ELetVar t)                = ELetVar (cleanup vs exs evs t)
           c (EBits val size)           = EBits val size
           c (ECon t)                   = ECon (cleanup vs exs evs t)
           c (EBitCon id es)            = EBitCon id (map (second c) es)
               where second f (x, y) = (x, f y)
           c (ELam i t e)               = ELam i (cleanType vs t) (c e)
           c (EMethod d n ts ds)        = EMethod (cleanup vs exs evs d)
                                                  n
                                                  (map (cleanType vs) ts)
                                                  (cleanup vs exs evs ds)
           c (ELet ds e)                = ELet (cleanup vs exs evs ds) (c e)
           c (ELetTypes cs e)           = ELetTypes cs' (cleanup ws exs evs e)
               where (ws, cs') = cleanTypeBinding vs cs
           c (ESubst exs' evs' e)       = cleanup vs (exs'++exs)
                                                  (evs'++evs)
                                                  e
           c (EMatch m)                 = EMatch (cleanup vs exs evs m)
           c (EApp f x)                 = EApp (c f) (c x)
           c (EBitSelect e f)           = EBitSelect (c e) f
           c (EBitUpdate e f e')        = EBitUpdate (c e) f (c e')
           c (EStructInit k fs)         = EStructInit k [(f, c e) | (f, e) <- fs]
           c (EBind ta tb tm me v e e') = EBind (cleanType vs ta) (cleanType vs tb) (cleanType vs tm)
                                                (cleanup vs exs evs me) v (c e) (c e')
           c (EReturn e)                = EReturn (c e)

instance Cleanup Ev
  where cleanup vs exs evs (EvVar i)         = fromMaybe (EvVar i) (cleanup vs exs evs `fmap` lookup i evs)
        cleanup vs exs evs (EvCons t)        = EvCons (cleanup vs exs evs t)
        cleanup vs exs evs (EvRequired n es) = EvRequired n (map (cleanup vs exs evs) es)
        cleanup vs exs evs (EvCases cs)      = EvCases [(map cleanCond cond, cleanup vs exs evs ev) | (cond, ev) <- cs]
            where cleanCond (kid, t) = (kid, cleanType (kid:vs) t)
        cleanup vs _   _   e@(EvComputed {}) = e
        cleanup vs exs evs (EvFrom EvWild e e') = EvFrom EvWild (cleanup vs exs evs e) (cleanup vs exs evs e')
        cleanup vs exs evs (EvFrom p@(EvPat _ ts _) e e') = EvFrom p (cleanup vs exs evs e) (cleanup vs' exs evs e')
            where vs' = tvs ts ++ vs

instance Cleanup t => Cleanup (Gen t)
  where cleanup vs exs evs (Gen ts' es t) = Gen ts' es (cleanup (ts' ++ vs) exs evs t)

instance Cleanup Inst
  where cleanup vs exs evs (Inst i ts es)
          = Inst i (map (cleanType vs) ts) (cleanup vs exs evs es)

--------------------------------------------------------------------------------
-- Matches
--------------------------------------------------------------------------------

instance Cleanup Match
  where cleanup vs exs evs MFail          = MFail
        cleanup vs exs evs (MCommit e)    = MCommit (cleanup vs exs evs e)
        cleanup vs exs evs (MElse m1 m2)  = MElse (cleanup vs exs evs m1)
                                                   (cleanup vs exs evs m2)
        cleanup vs exs evs (MGuarded (GSubst evs') m)
                                       = cleanup vs exs (evs' ++ evs) m
        cleanup vs exs evs (MGuarded (GLetTypes cs) m)
                                       = MGuarded (GLetTypes cs') (cleanup ws exs evs m)
            where (ws, cs') = cleanTypeBinding vs cs
        cleanup vs exs evs (MGuarded g m) = MGuarded (cleanup vs exs evs g)
                                                      (cleanup vs exs evs m)


--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

instance Cleanup Pattern
  where cleanup vs exs evs PWild          = PWild
        cleanup vs exs evs (PVar i s)     = PVar i (cleanType vs s)
        cleanup vs exs evs (PCon inst is) = PCon (cleanup vs exs evs inst) is

--------------------------------------------------------------------------------
-- Guards
--------------------------------------------------------------------------------

instance Cleanup Guard
  where cleanup vs exs evs (GFrom p id)   = GFrom (cleanup vs exs evs p) id
        cleanup vs exs evs (GLet ds)      = GLet (cleanup vs exs evs ds)

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

instance Cleanup Defn
  where cleanup vs exs evs (Defn i s (Left (name, ts)))
          = Defn i (cleanType vs s) (Left (name, map (cleanType vs) ts))
        cleanup vs exs evs (Defn i s (Right body))
          = Defn i (cleanType vs s) (Right (cleanup vs exs evs body))

instance Cleanup Decls
  where cleanup vs exs evs (Decls defns) = Decls (cleanup vs exs evs defns)

--------------------------------------------------------------------------------
-- Top-level declarations
--------------------------------------------------------------------------------

instance Cleanup (Program KId)
  where cleanup vs exs evs p = p { decls = cleanup vs exs evs (decls p) }
