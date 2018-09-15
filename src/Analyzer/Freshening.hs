{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Analyzer.Freshening (freshenProgram, ScopeEnv) where

-- This module freshens variable bindings by uniquely renaming each
-- one.  It does not touch type names, constructor names or field
-- names since those are global.  It also does not rename global
-- variables, though it would be reasonable to do so.  The only reason
-- it does not rename global variables is to keep variable names a
-- little cleaner.

-- It may make sense to have checks to be sure that type and
-- constructor names are in scope.  For now I'm leaving that to the
-- future.

import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.Generics hiding (Fixity)
import Data.List
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Map as Map

import Common
import Printer.Common ((<+>), text)
import Printer.Surface
import Syntax.Common hiding (Pred)
import Syntax.Surface

type M a = ReaderT (Map.Map Id Id) Base a

-- There are two good optimizations not implemented here:
--  1. Only freshen variables that shadow other variables.
--     Implement this by storing 'Nothing' for a variable in scope but not
--     renamed, and 'Just' for a renamed variable.
--  2. Reuse sub-expressions that don't change.
-- These two optimizations only benefit when used together and even
-- then reduce only the allocation, not the time for the analysis.

-- Scoping isn't very interesting yet, as we don't have any kind of namespace system.  All we're
-- doing yet is replacing names that shadow higher-level declarations with auto-generated (but
-- recognizable) names.  For example, the declarations:
--    f x = let x = 5 in x
-- would be transformed into
--    f x = let x$1 = 5 in x$1
-- We don't do any kind of renaming on types, as there's currently no notion of scoping for types or
-- type variables.
--
-- By mapping to a "Located Id" we store where the Id was defined for when
-- we issue redefinition errors.

type ScopeEnv = ([Located Id], [Located Id]) -- (public identifiers, private identifiers)

rejectDuplicates :: [Located Id] -> [Located Id] -> Base ()
rejectDuplicates scope ids =
    case duplicates scope ids of
      [] -> return ()
      ds -> failWithS (unlines [fromId id ++ " defined at both " ++ show l ++ " and " ++ show l' | (id, l, l') <- ds])
    where duplicates seen [] = []
          duplicates seen (At s id : ids) =
              let dups = duplicates (At s id : seen) ids
              in case locIn id seen of
                   Just s' -> (id, s, s') : dups
                   Nothing -> dups

          locIn _ [] = Nothing
          locIn id (At loc id' : rest)
              | id == id' = Just loc
              | otherwise = locIn id rest

-- This is the main entry point for this module, but it is merely a driver
-- for the freshenProgram' function, which is the main workhorse of this module.
-- Most of the work of freshenProgram is just setting up the right environments
-- for freshenProgram' to use.
freshenProgram :: Has s ScopeEnv => Pass s Program Program
freshenProgram = up body
    where body p = do (oldGlobals, oldPrivates) <- get
                      let declVars = declsExternalVars (decls p)
                          classMethods = [At s id | At s (Class _ _ _ (Just d)) <- classes p, Signature id _ <- signatures d]
                          opaqueDataMethods = [At s id | At s (Datatype _ _ _ (Just ds)) <- datatypes p, Signature id _ <- signatures ds]
                          opaqueSynonymMethods = [At s id | At s (Synonym _ _ (Just ds)) <- synonyms p, Signature id _ <- signatures ds]
                          areaNames = concat [map fst inits | At _ (Area _ inits _ _) <- areas p]
                          (publicPrimNames, privatePrimNames) = partitionEithers $ concatMap bindingsFromPrimitive (primitives p)
                          newGlobals = declVars ++ classMethods ++ opaqueDataMethods ++ opaqueSynonymMethods ++ areaNames ++ publicPrimNames
                      liftBase (rejectDuplicates (oldGlobals ++ oldPrivates) (newGlobals ++ privatePrimNames))
                      put (oldGlobals ++ newGlobals, oldPrivates ++ privatePrimNames)
                      liftBase (runReaderT (freshenProgram' p) (Map.fromList [(dislocate id, dislocate id) | id <- oldGlobals ++ newGlobals ++ privatePrimNames]))

bindingsFromPrimitive (At s (PrimValue (Signature id _) _ True)) = [Left (At s id)]
bindingsFromPrimitive (At s (PrimValue (Signature id _) _ False)) = [Right (At s id)] -- private
bindingsFromPrimitive (At _ (PrimCon {})) = []
bindingsFromPrimitive (At _ (PrimType _)) = []
bindingsFromPrimitive (At s (PrimClass _ _ _ (Just d))) = [Left (At s id) | Signature id _ <- signatures d]
bindingsFromPrimitive (At _ (PrimClass _ _ _ Nothing)) = []

----------------------------------------------------------------------------------------------------
-- WithFresh: Adds substitutions to freshen variables
----------------------------------------------------------------------------------------------------

-- The way freshenProgram' works is to recur down the tree and when it finds
-- a binding form, it creates fresh identifiers for every identifier bound
-- by that binding form.  The "withFresh" function implements the job
-- of finding the bound variables

class WithFresh a where
  withFresh :: a -> M b -> M b

-- The "withFreshVars" function implements the job of creating fresh identifiers
-- and adding them to the environment.  It is like "withFresh" but has to be explicitly
-- given the variables to be freshened.  "withFresh" is usually implemented in terms
-- of "withFreshVars".
withFreshVars :: [Id] -> M a -> M a
withFreshVars vars m = do
  env <- ask
  let xs = nub (sort vars)
  xs' <- mapM fresh xs
  local (\_ -> foldr (\ (old, new) env -> Map.insert old new env) env $ zip xs xs') $ m

-- "freshenId" replaces an "Id" with it's binding in the environment.
freshenId env id | Just id' <- Map.lookup id env = return (maybe id' (flip setFixity id') (getFixity id))
                 | otherwise = failWithS ("Unbound variable " ++ fromId id)

instance WithFresh Decls where withFresh d = withFreshVars (map dislocate $ declsExternalVars d)

-- Normally, we would use 'bound' from the 'Binder' class to determine the bound
-- identifiers in a Decls.  However, consider the following code:
--    let f x y = <rhs>
--    in <body>
-- Here 'f', 'x', and 'y' are bound in <rhs>, but only 'f' is bound in <body>.
-- The 'bound' method returns all three of 'f', 'x', and 'y', but for our purposes
-- we only want to know about 'f'.  Thus we have to implement a special version ourselves.
declsExternalVars :: Decls -> [Located Id]
declsExternalVars Decls{ equations = es } =
    nubBy (\x y -> dislocate x == dislocate y) $ -- this will be first occurrence since sortBy is stable
    sortBy (\x y -> dislocate x `compare` dislocate y) $
    concatMap equationExternalVars es
  where equationExternalVars (lhs := rhs)
            | (At s (PVar f), args) <- flattenPattern lhs = [At s f] -- function or simple variable
            | otherwise = bound lhs -- anything else
        bound (At s (PVar id))           = [At s id]
        bound (At s (PAs id p))          = At s id : bound p
        bound (At s (PTyped p _))        = bound p
        bound (At s (PTuple ps))         = concatMap bound ps
        bound (At s (PApp p p'))         = bound p ++ bound p'
        bound (At s (PLabeled _ ps))     = concatMap (\(At _ (FieldPattern _ p)) -> bound p) ps
        bound (At s (PInfix first rest)) = bound first ++
                                           filter (not . isConId . dislocate) operators ++
                                           concatMap bound operands
            where (operators, operands) = unzip rest
        bound p                          = []

instance WithFresh Pattern where withFresh p = withFreshVars (bound p)

instance (WithFresh a) => WithFresh [a] where
    withFresh [] = id
    withFresh (x : xs) = withFresh x . withFresh xs
instance (WithFresh a) => WithFresh (Maybe a) where
    withFresh Nothing = id
    withFresh (Just x) = withFresh x
instance (WithFresh a) => WithFresh (Located a) where
    withFresh (At _ a) = withFresh a

----------------------------------------------------------------------------------------------------
-- Freshen: makes all variables fresh and not shadowing
----------------------------------------------------------------------------------------------------

-- "freshenProgram'" is the main workhorse of this module.  It is
-- written using SYB, so it id defined in terms of several helper
-- functions that do the job for each type (e.g., pattern for Pattern
-- expr for Expr, etc.).
--
-- Some clauses that are good examples of various aspects of this
-- algorithm are:
--
--  * ELet: Uses 'withFreshDecls' to find and freshen variables in the
--          'decls', then continues the recursion with 'gmapM'
--
--  * EBind: Uses 'withFreshVars' to explicitly set the fresh variables
--           and then continues the recursion with 'gmapM'.
--
--  * ECon: Stops the recursion so that it does *not* go into the "Id"
--          in the constructor.  This is important because we don't
--          want to try to substitute constructor identifiers and
--          doing so would likely result in an unbound identifier
--          error.
--
--  * The "_" clause of 'expr': This is the default action when no
--         special processing is needed.
--
-- Note that because we use the "somewhere" traversal, the automatic
-- recursive traversal stops when it reaches a type that has a helper
-- function.  In order to continue the recursion the 'rec' function is
-- handed to these helper functions.  There are two typical ways to
-- use this function.
--
-- The first is 'rec located_pattern'.  This does a recursion over the
-- 'located_pattern' object that has type 'Located Pattern'.
--
-- The second is 'gmapM rec rhs'.  This does a recursion over the
-- *children* of the 'rhs' object that has type 'Rhs'.  Recurring over
-- children instead of the object itself is often important to avoid
-- an infinite loop that just keeps recurring over the same object
-- over and over again.

freshenProgram' :: Program -> M Program
freshenProgram' = rec where
  localize :: (Data a) => Located a -> M (Located a)
  localize (At l x) = return (At l) `ap` (failAt l (rec x))
  rec :: (Data a) => a -> M a
  rec = gmapM rec
        -- Types that don't contain Id needing freshening
        `extM` (return :: String -> M String)
        `extM` (return :: Bool -> M Bool)
        `extM` (return :: Int -> M Int)
        `extM` (return :: Type -> M Type)
        `extM` (return :: Pred -> M Pred)
        `extM` (return :: ClassConstraint -> M ClassConstraint)
        `extM` (return :: Fundep Id -> M (Fundep Id))
        `extM` (return :: Literal -> M Literal)
        -- SYB doesn't have a convenient way to apply 'localize' to every type of the
        -- form 'Located a' so we have to explicitly list all of them here. (Ugh.)
        `extM` (localize :: Located Area -> M (Located Area))
        `extM` (localize :: Located Bitdatatype -> M (Located Bitdatatype))
        `extM` (localize :: Located Class -> M (Located Class))
        `extM` (localize :: Located ClassConstraint -> M (Located ClassConstraint))
        `extM` (localize :: Located Datatype -> M (Located Datatype))
        `extM` (localize :: Located Expr -> M (Located Expr))
        `extM` (localize :: Located FieldPattern -> M (Located FieldPattern))
        `extM` (localize :: Located Fixity -> M (Located Fixity))
        `extM` (localize :: Located (Fundep Id) -> M (Located (Fundep Id)))
        `extM` (localize :: Located Id -> M (Located Id))
        `extM` (localize :: Located Instance -> M (Located Instance))
        `extM` (localize :: Located Kind -> M (Located Kind))
        `extM` (localize :: Located Literal -> M (Located Literal))
        `extM` (localize :: Located Pattern -> M (Located Pattern))
        `extM` (localize :: Located Pred -> M (Located Pred))
        `extM` (localize :: Located Primitive -> M (Located Primitive))
        `extM` (localize :: Located Requirement -> M (Located Requirement))
        `extM` (localize :: Located [String] -> M (Located [String]))
        `extM` (localize :: Located Struct -> M (Located Struct))
        `extM` (localize :: Located Synonym -> M (Located Synonym))
        `extM` (localize :: Located Pred -> M (Located Pred))
        `extM` (localize :: Located Type -> M (Located Type))
        -- Types that contain Id
        `extM` pattern `extM` fieldPattern
        -- Types that need their variables renamed
        `extM` id `extM` fixities `extM` expr
        -- Types containing decls
        `extM` rhs `extM` area `extM` primitive `extM` program
        -- Types containing patterns
        `extM` alt `extM` equation
  pattern e@(PCon _) = return e
  pattern (PLabeled ctor ps) = return PLabeled `ap` return ctor `ap` mapM rec ps
  pattern e = gmapM rec e
  fieldPattern (FieldPattern id p) = return (FieldPattern id) `ap` rec p
  id i = do env <- ask; freshenId env i
  fixities (Fixities vf tf) = do
    env <- asks (\env id -> Map.findWithDefault (error $ "Internal error: Unbound variable: " ++ show id) id env)
    return $ Fixities (Map.mapKeys env vf) tf -- Type names do not get freshened
  expr e@(ELet decls _) = withFresh decls $ gmapM rec e
  expr e@(EIf (ScFrom (Just x) _) _ _) = withFreshVars [x] $ gmapM rec e
  expr e@(ECase (ScFrom (Just x) _) _) = withFreshVars [x] $ gmapM rec e
  expr e@(ELam pats _) = withFresh pats $ gmapM rec e
  expr e@(EBind (Just x) _ _) = withFreshVars [x] $ gmapM rec e
  expr e@(ECon _) = return e
  expr (ESelect e f) = return ESelect `ap` rec e `ap` return f
  expr (EUpdate e es) =
      return EUpdate `ap` rec e `ap` mapM  (\(x,y) -> rec y >>= \y' -> return (x, y')) es
  expr  (EStructInit ctor es) =
      return EStructInit `ap` return ctor `ap` mapM  (\(x,y) -> rec y >>= \y' -> return (x, y')) es
  expr e = gmapM rec e
  rhs e@(Unguarded _ d) = withFresh d $ gmapM rec e
  rhs e@(Guarded _ d) = withFresh d $ gmapM rec e
  -- Note that we do *not* do withFresh on the decls in Class and
  -- Instance since the Decls in them are really top level
  -- Likewise, every Decls depends on the surrounding context to call withFresh on the Decls
  area e@(Area _ _ _ d) = withFresh d $ gmapM rec e
  primitive e@(PrimClass _ _ _ d) = withFresh d $ gmapM rec e
  primitive e@(PrimCon {}) = return e
  primitive e = gmapM rec e
  program e = do
    d <- rec (decls e)
    c <- rec (classes e)
    i <- rec (instances e)
    a <- rec (areas e)
    p <- rec (primitives e)
    return (e { decls = d, classes = c, instances = i, areas = a, primitives = p })
  alt e@(pat :-> _) = withFresh pat $ gmapM rec e
  equation e@(pat := rhs) = withFreshVars internalVars $ gmapM rec e
      where internalVars = case flattenPattern pat of
                             (At _ (PVar _), args) -> concatMap bound args
                             _ -> []
