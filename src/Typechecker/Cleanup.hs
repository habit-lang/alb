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

cleanupProgram :: Pass st (Program KId) (Program KId)
cleanupProgram = return . cleanup [] []

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

class Cleanup e
  where cleanup :: ExprSubst -> EvSubst -> e -> e

instance Cleanup t => Cleanup [t]
  where cleanup exs evs = map (cleanup exs evs)

instance Cleanup t => Cleanup (Id, t)
  where cleanup exs evs (i, t) = (i, cleanup exs evs t)

instance Cleanup Expr
  where cleanup exs evs = c
          where
           c (ELamVar i)                = fromMaybe (ELamVar i) (lookup i exs)
           c (ELetVar t)                = ELetVar (cleanup exs evs t)
           c (EBits val size)           = EBits val size
           c (ECon t)                   = ECon (cleanup exs evs t)
           c (ELam i t e)               = ELam i t (c e)
           c (EMethod d n ts ds)        = EMethod (cleanup exs evs d)
                                                  n
                                                  ts
                                                  (cleanup exs evs ds)
           c (ELet ds e)                = ELet (cleanup exs evs ds) (c e)
           c (ELetTypes cs e)           = ELetTypes cs (c e)
           c (ESubst exs' evs' e)       = cleanup (cleanup exs evs exs'++exs)
                                                  (cleanup exs evs evs'++evs)
                                                  e
           c (EMatch m)                 = EMatch (cleanup exs evs m)
           c (EApp f x)                 = EApp (c f) (c x)
           c (EBind ta tb tm me v e e') = EBind ta tb tm (cleanup exs evs me) v (c e) (c e')

instance Cleanup Ev
  where cleanup exs evs (EvVar i)         = fromMaybe (EvVar i) (lookup i evs)
        cleanup exs evs (EvCons t)        = EvCons (cleanup exs evs t)
        cleanup exs evs (EvRequired n es) = EvRequired n (map (cleanup exs evs) es)
        cleanup exs evs (EvCases cs)      = EvCases [(cond, cleanup exs evs ev) | (cond, ev) <- cs]
        cleanup _   _   e@(EvComputed {}) = e
        cleanup exs evs (EvFrom p e e')   = EvFrom p (cleanup exs evs e) (cleanup exs evs e')

instance Cleanup t => Cleanup (Gen t)
  where cleanup exs evs (Gen ts es t) = Gen ts es (cleanup exs evs t)

instance Cleanup Inst
  where cleanup exs evs (Inst i ts es)
          = Inst i ts (cleanup exs evs es)

--------------------------------------------------------------------------------
-- Matches
--------------------------------------------------------------------------------

instance Cleanup Match
  where cleanup exs evs MFail          = MFail
        cleanup exs evs (MCommit e)    = MCommit (cleanup exs evs e)
        cleanup exs evs (MElse m1 m2)  = MElse (cleanup exs evs m1)
                                                   (cleanup exs evs m2)
        cleanup exs evs (MGuarded (GSubst evs') m)
                                       = cleanup exs (cleanup exs evs evs' ++ evs) m
        cleanup exs evs (MGuarded g m) = MGuarded (cleanup exs evs g)
                                                      (cleanup exs evs m)


--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

instance Cleanup Pattern
  where cleanup exs evs PWild                 = PWild
        cleanup exs evs (PVar i s)            = PVar i s
        cleanup exs evs (PCon c ts ebinds is) = PCon c ts ebinds is

--------------------------------------------------------------------------------
-- Guards
--------------------------------------------------------------------------------

instance Cleanup Guard
  where cleanup exs evs (GFrom p e)    = GFrom (cleanup exs evs p)
                                                   (cleanup exs evs e)
        cleanup exs evs (GLet ds)      = GLet (cleanup exs evs ds)
        cleanup exs evs (GLetTypes cs) = GLetTypes cs

--------------------------------------------------------------------------------
-- Declarations
--------------------------------------------------------------------------------

instance Cleanup Defn
  where cleanup exs evs (Defn i s body)
          = Defn i s (cleanup exs evs `fmap` body)

instance Cleanup Decls
  where cleanup exs evs (Decls defns) = Decls (cleanup exs evs defns)

--------------------------------------------------------------------------------
-- Top-level declarations
--------------------------------------------------------------------------------

instance Cleanup (Program KId)
  where cleanup exs evs p = p { decls = cleanup exs evs (decls p) }

