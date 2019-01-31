{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}

module Analyzer.Fixity (fixityProgram) where

-- This module resolves the fixities of infix forms (i.e. TyInfix, EInfix, and PInfix) and
-- replaces them with the appropriate application forms.

import Control.Monad.Reader
import Control.Monad.State
import Data.Generics hiding (Fixity)
import qualified Data.Map as Map

import Common
import Syntax.Common
import Syntax.Surface

type M a = ReaderT Fixities Base a

----------------------------------------------------------------------------------------------------
-- WithFixity: collects fixity info from an object
----------------------------------------------------------------------------------------------------

class WithFixity a where withFixity :: a -> M b -> M b

removeFixities old remove = Map.difference old (Map.fromList (map (\x -> (x, Fixity NoAssoc 0)) remove))

-- There is a subtle difference between withFixity on an Decl and
-- withFixity on an Pattern.  The former collects fixity info that is
-- visible outsize the Decl, but the later collects fixity info
-- visible when in the scope bound by the pattern.

instance WithFixity Decls where
    withFixity d = local f
        where f old = Fixities { -- Note that Map.union is left biased so the new ones override any old ones
                                 valFixities = Map.union (valFixities (fixities d)) $
                                               removeFixities (valFixities old) $
                                               concat [externalPatternVars p | p := _ <- equations d],
                                 typeFixities = Map.union (typeFixities (fixities d)) $
                                                typeFixities old }

              externalPatternVars :: Located Pattern -> [Id]
              externalPatternVars p | Just b <- isFunctionPattern (dislocate p) = b
                                    | otherwise = bound p

              isFunctionPattern (PAs id p) | Just b <- isFunctionPattern (dislocate p) = Just (id : b)
                                           | otherwise = Nothing
              isFunctionPattern (PTyped p _) = isFunctionPattern (dislocate p)
              isFunctionPattern (PApp p _) = isFunctionPattern (dislocate p)
              isFunctionPattern (PInfix first rest) =
                  case filter (not . isConId) (map dislocate (fst (unzip rest))) of
                    [] -> Nothing
                    xs -> Just xs
              isFunctionPattern (PVar id) = Just [id]
              isFunctionPattern _ = Nothing

instance WithFixity Pattern where
    withFixity p = local f
        where f old = Fixities { valFixities = removeFixities (valFixities old) (bound p),
                                   typeFixities = typeFixities old }

instance WithFixity Id where
    withFixity x = local f
        where f old = Fixities { valFixities = Map.delete x (valFixities old),
                                   typeFixities = typeFixities old }

instance (WithFixity a) => WithFixity (Maybe a) where
    withFixity Nothing = id
    withFixity (Just a) = withFixity a

instance (WithFixity a) => WithFixity [a] where
    withFixity [] = id
    withFixity (x : xs) = withFixity x . withFixity xs

instance (WithFixity a) => WithFixity (Located a) where
    withFixity (At s a) = withFixity a

----------------------------------------------------------------------------------------------------
-- Associativity resolving
----------------------------------------------------------------------------------------------------

-- The resolveInfix function handles the interesting parts of resolving associativity.  This
-- function is used when resolving associativity in either types, patterns, or expressions, so
-- there's a bit of extra generality: in particular, it takes three constructors as arguments, used
-- to construct applications, constructors, and variables appropriately.

-- This type is only used as the result of tighter (below)
data Result = First | Second | Neither

resolveInfix :: (Id -> Bool)                -- Predicate distinguishing constructor names
             -> Map.Map Id (Located Fixity) -- Relevant fixity map
             -> (t -> t -> t)               -- Application constructor
             -> (Located Id -> t)           -- Constructor constructor
             -> (Located Id -> t)           -- Variable constructor
             -> t                           -- Left-most subexpression
             -> [(Located Id, t)]           -- Remaining operators and subexpressions
             -> M t
resolveInfix _ _ _ _ _ _ [] = error "resolveInfix called with empty tail"
resolveInfix isConId fixities app con var lhs ((op,rhs):tail) =
    case loop [(lhs,op)] rhs tail of
      Left (At loc id1, At _ id2) ->
          failWithS ("At " ++ show loc ++ ": " ++
                     "inconsistent fixities for operators " ++ fromId id1 ++
                     " and " ++ fromId id2)
      Right t                     -> return t
    where fixity (At loc s) = maybe (Fixity LeftAssoc 9) dislocate (Map.lookup s fixities)
          app2 lhs op rhs = app (app (if isConId (dislocate op) then con op' else var op') lhs) rhs
              where op' = fmap (setFixity (fixity op)) op

          tighter op0 op1
              | fix0 > fix1 = First
              | fix0 < fix1 = Second
              | otherwise = case (assoc0, assoc1) of
                              (LeftAssoc, LeftAssoc)   -> First
                              (RightAssoc, RightAssoc) -> Second
                              _                        -> Neither
              where Fixity assoc0 fix0 = fixity op0
                    Fixity assoc1 fix1 = fixity op1

          -- The basic idea is that we maintain a stack of (expr, operator) pairs on the left, the
          -- current expression (e), and a tail of (operator, expr) pairs to the right.  At each step,
          -- we have three options:
          --  - The operator at the top of the stack binds more tightly than that at the top of the
          --    tail.  In that case, we pop (e0, op0) from the stack, replace the current expression
          --    with (e0 op0 e), and loop;
          --  - The operator at the top of the tail binds more tightly than either the operator at
          --    the top of the stack or the operator following it in the tail.  In that case, we pop
          --    (op1, e1) from the tail, replace the current expression with (e op1 e1), and loop;
          --    or,
          --  - The second operator in the tail binds more tightly than either of the others; in
          --    that case, we pop (op1, e1) from the tail, push (e, op) onto the stack, and loop
          --    with e1 as the current expression.

          loop [] e []                 = Right e
          loop ((lhs,op):stack) rhs [] = loop stack (app2 lhs op rhs) []
          loop [] e [(op1,e1)]         = Right (app2 e op1 e1)
          loop [] e ((op1,e1):tail@((op2,_):_)) =
              case tighter op1 op2 of
                First -> loop [] (app2 e op1 e1) tail
                Second -> loop [(e,op1)] e1 tail
                Neither -> Left (op1, op2)
          loop ((e0,op0):stack) e [(op1,e1)] =
              case tighter op0 op1 of
                First   -> loop stack (app2 e0 op0 e) [(op1,e1)]
                Second  -> loop ((e0,op0):stack) (app2 e op1 e1) []
                Neither -> Left (op0, op1)
          loop ((e0,op0):stack) e ((op1,e1):tail@((op2,_):_)) =
              case tighter op0 op1 of
                First   -> loop stack (app2 e0 op0 e) ((op1,e1):tail)
                Second  -> case tighter op1 op2 of
                             First   -> loop ((e0,op0):stack) (app2 e op1 e1) tail
                             Second  -> loop ((e,op1):(e0,op0):stack) e1 tail
                             Neither -> Left (op1,op2)
                Neither -> Left (op0,op1)

----------------------------------------------------------------------------------------------------
-- fixityProgram: eliminates infix expressions
----------------------------------------------------------------------------------------------------


fixityProgram' :: Program -> M Program
fixityProgram' = rec where
  rec :: (Data a) => a -> M a
  rec = gmapM rec
        `extM` (return :: String -> M String)
        `extM` (return :: SourcePos -> M SourcePos)
        `extM` (return :: Kind -> M Kind)
        -- Types with infix forms to be removed
        `extM` typ `extM` expr `extM` pattern
        -- Types containing patterns
        `extM` equation `extM` alt
        -- Types containing decls
        -- Note that we do *not* do withFixity on the decls in Class and Instance here since the Decls in them are really top level
        -- TODO: do when (not (fixitiesEmpty (fixities decls))) $ failWithS "Unexpected fixity declaration in class declaration"
        `extM` rhs `extM` area `extM` primitive `extM` program
  typ (TyInfix head tail) = do
    fixities <- asks typeFixities
    At _ t' <- resolveInfix isTyConId fixities (\t1 t2 -> at t1 (TyApp t1 t2)) (fmap TyCon) (fmap TyVar) head tail
    rec t'
  typ t = gmapM rec t
  expr e@(ELet decls _) = withFixity decls $ gmapM rec e
  expr e@(ELam pats _) = withFixity pats $ gmapM rec e
  expr e@(EBind x _ _) = withFixity x $ gmapM rec e
  expr (EInfix head tail) = do
    fixities <- asks valFixities
    At _ e' <- resolveInfix isConId fixities (\e1 e2 -> at e1 (EApp e1 e2)) (fmap ECon) (fmap EVar) head tail
    rec e'
  expr e = gmapM rec e
  pattern (PInfix head tail) = do
    fixities <- asks valFixities
    At _ p' <- resolveInfix isConId fixities (\p1 p2 -> at p1 (PApp p1 p2)) (fmap PCon) (fmap PVar) head tail
    rec p'
  pattern p = gmapM rec p
  equation e@(lhs := rhs) = withFixity lhs $ gmapM rec e
  alt e@(pat :-> _) = withFixity pat $ gmapM rec e
  rhs e@(Unguarded _ d) = withFixity d $ gmapM rec e
  rhs e@(Guarded _ d) = withFixity d $ gmapM rec e
  area e@(Area _ _ _ _ d) = withFixity d $ gmapM rec e
  primitive e@(PrimClass _ _ _ d) = withFixity d $ gmapM rec e
  primitive e = gmapM rec e
-- TODO: do when (not (fixitiesEmpty (fixities decls))) $ failWithS "Unexpected fixity declaration in class declaration"
  program e = withFixity (decls e) $ gmapM rec e

fixityProgram :: Has s Fixities => Pass s Program Program
fixityProgram = up (\p -> do globalFixities <- get
                             put (mergeFixities globalFixities (fixities (decls p)))
                             liftBase $ runReaderT (fixityProgram' p) globalFixities)
