{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Fidget.TailCalls (tailCallOpt) where

{---------------------------------------

This file converts known, tail calls into label jumps.

Given how Fidget works, it is impossible to eliminate all tail calls
without majorly restructuring each program, so we make the following
approximation.

First, we consider only known tail calls.  We do not try to optimize
tail calls to first class uses to functions.

Second, of the remaining tail calls we guarantee that the number of
frames on the dynamic stack is no more than twice the number of frames
that would be if all tail calls were eliminates (except for
first-class tail calls).

We do this by taking each 'letrec' binding group and creating
a 'letlabel' binding group for the body of the letrec and
the bodies of each function defined in that letrec.

The consequence of this is that a tail-call that does
not go "up" past a lambda, can always be converted to a goto.

We cannot eliminate the tail-calls that do go "up" past a lambda, but
it is a fairly simply proof to show that for every such call there had
to be a "down" call into the lambda which was not itself a tail call.
Thus for every tail call that we do not optimize there is at least one
corresponding non-tail call and thus the size of the dynamic stack is
no more than twice the size it would be if fully optimized.  (Though
again we are ignoring first-class tail calls.)

NOTE: Since we are copying code, this translation must be careful to
alpha rename all the bindings in the copied code.
----------------------------------------}

import Control.Monad.Writer
import Control.Monad.Reader
import Data.Generics
import qualified Data.Map as Map
import qualified Data.Set as Set

import Common
import Fidget.AST

------------------------------
-- Trivial Helpers
------------------------------

mkEletlabel [] body = body
mkEletlabel labels body = Eletlabel labels body

mkEletrec [] body = body
mkEletrec functions body = Eletrec functions body

onFst f (x,y) = (f x, y)
onSnd f (x,y) = (x, f y)

onSndM :: (Monad m) => (a -> m b) -> (c, a) -> m (c, b)
onSndM f (x,y) = f y >>= \y' -> return (x, y')

fst4 (x,_,_,_) = x

-----------------------------
-- Monadic Helpers
-----------------------------

-- CONVENTION: when we have a pair of a "tail" thing and a "non-tail"
-- thing, we put the "tail" thing first.

type M a = ReaderT (Map.Map Id Id, {- renaming environment for in-scope labels that replace tail calls -}
                    Map.Map Id Id) {- renaming environment for everything else that is in-scope -}
          (WriterT (Set.Set Id, {- referenced tail, uses pre-renaming names -}
                    Set.Set Id) {- referenced non-tail, uses pre-renaming names -}
             Base) a

-----------------------------
-- Stuff for keeping track of what identifiers are referenced
-----------------------------

-- Marks an identifier as being used in tail position
-- WARNING: takes the pre-renaming name and not the post-renaming name
tellTail :: Id -> M ()
tellTail x = tell (Set.singleton x, Set.empty)

-- Marks an identifier as being used in non-tail position
-- WARNING: takes the pre-renaming name and not the post-renaming name
tellNonTail :: Id -> M ()
tellNonTail x = tell (Set.empty, Set.singleton x)

-- Returns the identifiers used in tail position in a monadic action.
-- Also clears the list of identifiers used in tail position.
listenTail :: M a -> M (a, Set.Set Id)
listenTail m = censor (onFst (const Set.empty)) (listens fst m)

-- Returns the identifiers used in non-tail position in a monadic action.
-- Also clears the list of identifiers used in non-tail position.
listenNonTail :: M a -> M (a, Set.Set Id)
listenNonTail m = censor (onSnd (const Set.empty)) (listens snd m)

--------------------------------
-- Stuff for keeping track of the in-scope variable environment
--------------------------------

-- Modify the reader environment to contain no in-scope labels.  This
-- is used because we are not allowed to call a label defined outside
-- a lambda from inside that lambda.
noLabels :: M a -> M a
noLabels m = local (onFst (const Map.empty)) m

-- Get the label assigned for a function call that should be turned
-- into a tail call.
getLabel :: Id -> M (Maybe Id)
getLabel x = asks (Map.lookup x . fst)

-- Get the alpha renaming for a variable.
getVar :: Id -> M Id
getVar x = asks (Map.findWithDefault msg x . snd) where
  msg = error $ "INTERNAL ERROR: getVar: variable not in scope: " ++ show x

-- Lifted version of getVar for pairs.
getVarFst :: (Id, a) -> M (Id, a)
getVarFst (x, y) = getVar x >>= \x' -> return (x', y)

-- Lifted version of getLabel for pairs.
getLabelFst :: (Id, a) -> M (Id, a)
getLabelFst (x, y) = getLabel x >>= \(Just x') -> return (x', y)

-- Run a monadic action with a set of alpha renamed identifiers.
alpha :: [Id] -> M a -> M a
alpha vars m = do
  vars' <- mapM fresh vars
  censor (onSnd (\m -> foldr Set.delete m vars)) $
    local (onSnd (Map.union (Map.fromList (zip vars vars')))) $
      m

-- Run a monadic action with a set of alpha renamed identifiers to be
-- used by tail calls.
alphaTail :: [Id] -> M a -> M a
alphaTail vars m = do
  vars' <- mapM fresh vars
  censor (onFst (\m -> foldr Set.delete m vars)) $
    local (onFst (Map.union (Map.fromList (zip vars vars')))) $
      m

----------------------------
-- The core functions implementing tail calls
----------------------------

-- Make tail-callable labels for the functions given in 'bindings'.
makeTails :: [(Id, Function)] -> Expr -> M Expr
makeTails bindings body = alphaTail (map fst bindings) $ do
  (body', tail) <- listenTail $ tailCallExpr body
  labels <- iter (listenTail . tailCallLabelFunction) tellTail (Map.fromList bindings) tail
  labels' <- mapM getLabelFst (Map.toList labels)
  return $ mkEletlabel labels' body'

-- Iteratively build a set of bindings where new bindings may bring in
-- references to further bindings.
--
-- Given that 'needs' need to be in scope, select elements of
-- 'candidates' to be procesed by 'do_rhs'.  Also recursively select
-- more elements of 'candidates' that 'do_rhs' returns as also being
-- needed.  Finally, use 'tell' to report 'needs' that are not
-- satisfied by 'candidates'.
iter :: (e -> M (e, Set.Set Id)) -> (Id -> M ()) -> Map.Map Id e -> Set.Set Id -> M (Map.Map Id e)
iter do_rhs tell candidates needs = go Map.empty (Set.toList needs) where
  -- candidates = bindings that we can use to add to 'have'
  -- have = bindings that we already have
  -- needs = references that we need to add to 'have'
  --go :: Map.Map Id e -> [Id] -> M (Map.Map Id e)
  go have [] = return have
  go have (need:needs)
    -- This need is already satisfied
    | Map.member need have = go have needs
    -- This need can be satisfied locally
    | Just rhs <- Map.lookup need candidates = do
        (rhs', new_needs) <- do_rhs rhs
        go (Map.insert need rhs' have) (Set.toList new_needs ++ needs)
    -- This need couldn't be satisfied locally
    | otherwise = tell need >> go have needs

------------------------------------
-- Main Entry Point
------------------------------------

tailCallOpt :: [Id] -> Pass () Program Program
tailCallOpt exports program = liftM fst $ liftBase $
  runWriterT (runReaderT (tailCallProgram exports program) (Map.empty, Map.empty))

------------------------------------
-- Recursions for each type of term
------------------------------------

-- Nothing interesting here, except that the initial environment maps
-- top-levels to their own names.
--
-- TODO: for now 'exports' is ignored.  We can do better by using
-- 'iter' to generate code for only the function definitions that are
-- needed.
tailCallProgram :: [Id] -> Program -> M Program
tailCallProgram _exports (Program globals functions main init tconenv areas structs) = do
  let vars = map fst globals ++ map fst functions ++ map fst4 areas
  functions' <- local (const $ (Map.empty, Map.fromList (zip vars vars))) $
                mapM (onSndM (tailCallFundec [(x, f) | (x, Internal f) <- functions])) functions
  return (Program globals functions' main init tconenv areas structs)

-- Nothing interesting here, except that references need to be renamed and marked as used
tailCallAtom :: Atom -> M Atom
tailCallAtom = everywhereM (mkM f) where
  f (Agvar x t) = tellNonTail x >> getVar x >>= \x' -> return (Agvar x' t)
  f (Avar  x t) = tellNonTail x >> getVar x >>= \x' -> return (Avar  x' t)
  f x = return x

-- Nothing interesting here, except that Scall needs to mark it's function as used
tailCallSimplExpr (Satom a) = return Satom `ap` tailCallAtom a
tailCallSimplExpr (Scall sig f args) = return (Scall sig) `ap` getVar f `ap` mapM tailCallAtom args
tailCallSimplExpr (Sapp sig f args) = return (Sapp sig) `ap` tailCallAtom f `ap` mapM tailCallAtom args
tailCallSimplExpr (Salloc t n args) = return (Salloc t n) `ap` mapM tailCallAtom args

-- Nothing interesting here either
tailCallFundec :: [(Id, Function)] -> Fundec -> M Fundec
tailCallFundec bindings (External f) = return (External f)
tailCallFundec bindings (Internal f) = liftM Internal $ tailCallLetrecFunction bindings f

-- When we optimize a 'Function' defined by a 'letrec', we have to
-- both alpha rename its arguments and reset the in-scope labels to be
-- empty.  We then use 'makeTails' to process the body and create
-- 'letlabels' for elements of 'bindings' that can be used locally.
--
-- Note that if we have a function like:
--   (letrec ([f body]) ...)
-- Then the naive translation would duplicate body and look like:
--   (letlabel ([f body]) body)
-- A better translation which we do converts this to the following instead:
--   (letlabel ([f body]) (goto f))
tailCallLetrecFunction :: [(Id, Function)] -> Function -> M Function
tailCallLetrecFunction bindings f@(Function args ret body) = alpha (map fst args) $ noLabels $ do
  let lab = head [x | (x, f') <- bindings, f == f'] -- TODO: This is a bit of a hack
  body_lab <- fresh "body"
  body' <- makeTails bindings
           -- We translate to a tail call so the tailCallExpr in
           -- makeTails will translate it to Egoto
           (Elet body_lab ret
                     (Scall (Fsignature (map snd args) ret) lab (map (uncurry Avar) args))
                     (Eatom (Avar body_lab ret)))
  args' <- mapM getVarFst args
  return (Function args' ret body')

-- When we optimize a 'Function' defined by a 'letlabel', we have to
-- alpha rename the arguments, but otherwise nothing interesting
-- happens.
tailCallLabelFunction :: Function -> M Function
tailCallLabelFunction (Function args ret body) = alpha (map fst args) $ do
  body' <- tailCallExpr body
  args' <- mapM getVarFst args
  return (Function args' ret body')

-- tailCallExpr is where most of the interesting code is but these
-- first few clauses are uninteresting and just recur down the
-- expression while alpha renaming as necessary
tailCallExpr (Eatom a) = return Eatom `ap` tailCallAtom a
tailCallExpr (Eifthenelse a e1 e2) =
  return Eifthenelse `ap` tailCallAtom a `ap` tailCallExpr e1 `ap` tailCallExpr e2
tailCallExpr (Ecase atom alts def) =
  return Ecase `ap` tailCallAtom atom `ap` mapM go_alt alts `ap` go_def def
  where
    go_alt (x,n,e) = alpha [x] $ return (,,) `ap` getVar x `ap` return n `ap` tailCallExpr e
    go_def Nothing = return Nothing
    go_def (Just (x, e)) = alpha [x] $ liftM Just $ return (,) `ap` getVar x `ap` tailCallExpr e
tailCallExpr (Eixcase atom machint x e1 e2) = alpha [x] $
  return Eixcase `ap` tailCallAtom atom `ap` return machint
           `ap` getVar x `ap` tailCallExpr e1 `ap` tailCallExpr e2
tailCallExpr (Enzcase atom x e1 e2) = alpha [x] $
  return Enzcase `ap` tailCallAtom atom `ap` getVar x `ap` tailCallExpr e1 `ap` tailCallExpr e2
tailCallExpr (Erefcase atom area x e1 e2) = alpha [x] $
  return Erefcase `ap` tailCallAtom atom `ap` return area
           `ap` getVar x `ap` tailCallExpr e1 `ap` tailCallExpr e2
tailCallExpr (Eerror t) = return (Eerror t)
tailCallExpr (Eletlabel bindings body) = alpha (map fst bindings) $ do
  return Eletlabel `ap` mapM (getVarFst <=< onSndM tailCallLabelFunction) bindings
           `ap` tailCallExpr body
tailCallExpr (Egoto l args t) =
  tellTail l >> return Egoto `ap` getVar l `ap` mapM tailCallAtom args `ap` return t

-- The following clauses are were the code gets interesting.  When we
-- see an Elet, we check to see if it is a tail call.  If so, then we
-- try to create a call to Egoto.  Otherwise, we just recur as per
-- usual.
tailCallExpr (Elet lhs t rhs body) = alpha [lhs] $
  case (rhs, body) of
    -- These first two cases are for when it looks like a tail call
    (Scall sig f args, Eatom (Agvar x _)) | x == lhs -> mkGoto f args
    (Scall sig f args, Eatom (Avar  x _)) | x == lhs -> mkGoto f args
    _ -> mkLet
  where -- If it wasn't a tail call, then just recur down the Elet
        mkLet = return Elet `ap` getVar lhs `ap` return t
                       `ap` tailCallSimplExpr rhs
                       `ap` tailCallExpr body
        -- If it looks like a tail call and 'getLabel' tells us we have an in-scope binding,
        -- then create a call to Egoto.
        mkGoto x args = getLabel x >>= maybe mkLet
          (\x' -> tellTail x >> return (Egoto x') `ap` mapM tailCallAtom args `ap` return t)
-- When we see an Eletrec, we try to convert both the body of the
-- Eletrec and the body of each rhs of the Eletrec to have locally
-- defined labels for any contained tail calls.  We are also careful
-- to keep Eletrec bindings for only those bindings that are called in
-- non-tail positions.
tailCallExpr (Eletrec bindings body) = alpha (map fst bindings) $ do
  -- First, create letlabel for any tail calls in body
  (body', nonTails) <- listenNonTail $ makeTails bindings body
  -- Next, process the 'bindings' that are actually referenced as non-tail calls
  have <- iter (listenNonTail . tailCallLetrecFunction bindings)
            tellNonTail (Map.fromList bindings) nonTails
  have' <- mapM getVarFst (Map.toList have)
  return (mkEletrec have' body')
