{-# LANGUAGE FlexibleContexts, ParallelListComp, TupleSections, Rank2Types #-}

-- This module optimizes Fidget code doing constant folding, delay and let lifting, and inlining.

module Fidget.FidgetCleanup where

import Common (fresh, initial, localState, Pass, PassM(..))
import Fidget.AST
import Fidget.Typing

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Data.Bits ((.&.), (.|.), xor)
import Data.Generics
import Data.List (partition, nub)
import Data.Maybe (fromJust)
import qualified Data.Map as M

--DEBUG IMPORTS
--import Fidget.Pretty ({-instances only-})
--import Debug.Trace

-- The available ways to specify optimization passes. Used to hook
-- into the overall compiler pass structure.
data OptPasses = NoOpt | Full Int | Partial Int String

optFidget :: [Id] -> OptPasses -> Pass () Program Program
optFidget _ NoOpt p = return p
optFidget roots (Full n) p = opt n opts' p
    where opts' = foldr (>=>) return $ map ($ roots) $ map snd good_opts
optFidget roots (Partial n opts) p = opt n opts' p
    where opts' = foldr (>=>) return $ map ($ roots) $ map (\o -> fromJust $ lookup o all_opts) opts
          all_opts = good_opts ++ bad_opts

opt :: Int -> (Program -> PassM () Program) -> (Program -> PassM () Program)
opt 0 opts p = return p
opt n opts p = do
  p' <- opt (n-1) opts p
  p'' <- opts p'
  --trace ("opt:"++show n++":"++show (length (show p')) ++ "->" ++ show (length (show p''))) $ return ()
  return p''


-- options which are believed to be correct and reasonable to include
-- in the "Full" pass
good_opts = [
  ('c', const_fold_prog),
  ('d', lift_delay_prog),
  ('l', let_lift_prog),
  ('i', inline_prog')
  ]

-- options which are known to be wrong and should not be included in
-- the "Full" pass but are selectable from the command line for
-- testing.
bad_opts = []

-- Helper functions for SYB code
-- Top-down version of everywhereM
everywhereM' :: Monad m => GenericM m -> GenericM m
everywhereM' f x = f x >>= gmapM (everywhereM' f)

everywhereButM' :: (Monad m) => GenericQ Bool -> GenericM m -> GenericM m
everywhereButM' q f x
  | q x = return x
  | otherwise = f x >>= gmapM (everywhereM' f)

runSomewhere :: (a -> Maybe a) -> a -> a
runSomewhere f e = maybe e id (f e)

runSomewhereM :: (Monad m) => (a -> ExceptT String m a) -> a -> m a
runSomewhereM f e = do
  e' <- runExceptT (f e)
  case e' of
    Left _ -> return e
    Right e'' -> return e''

{------------------------------------------------------------------------

Delay lifting

This transformation hoists delay functions above atomic operations to
expose the delays at a higher level. The hope is that this will
improve the opportunities for uncurrying and other optimizations.

Older versions of this code considered Eerror to be a form of delay to
be lifted.  In general that isn't semantically valid, but future
versions may want to consider when it can be done.

------------------------------------------------------------------------}

lift_delay_prog :: [Id] -> Program -> PassM () Program
lift_delay_prog _ p = return $ everywhere (mkT lift_delay) (pre_lift_delay p)

-- Remove all unit vars so delay lifting is simpler
pre_lift_delay :: Program -> Program
pre_lift_delay = everywhere (mkT f) where
  f (Avar _ Funit) = Aconst Ounit
  f a = a

-- The branching case: convert a branching expression with delays in
-- each branch into a delayed branching instruction
lift_delay :: Expr -> Expr
lift_delay (Elet i t a@(Satom _) e) = lift_delay1 (Elet i t a) e
  -- ^ TODO: old code checked to be sure i wasn't recursive, but I don't see why
lift_delay (Eletrec fs e) = lift_delay1 (Eletrec fs) e
  -- ^ TODO: this may cause extra closure allocation
-- Eletlabel would be unreferenced if the body of the Eletlabel were a delay
-- thus inlining would have taken care of it and we don't handle it here
lift_delay (Eifthenelse a e1 e2)   = lift_delay2 (Eifthenelse a  ) e1 e2
lift_delay (Eixcase  a n  i e1 e2) = lift_delay2 (Eixcase  a n  i) e1 e2
lift_delay (Enzcase  a    i e1 e2) = lift_delay2 (Enzcase  a    i) e1 e2
lift_delay (Erefcase a ar i e1 e2) = lift_delay2 (Erefcase a ar i) e1 e2
lift_delay (Ecase a bs Nothing) = lift_delay' ctor [e | (_, _, e) <- bs] where
  ctor bs' = Ecase a [(i, n, e') | (i, n, _) <- bs | e' <- bs'] Nothing
lift_delay (Ecase a bs (Just (id,e))) = lift_delay' ctor (e:[e | (_, _, e) <- bs]) where
  ctor (e:bs') = Ecase a [(i, n, b') | (i, n, _) <- bs | b' <- bs'] (Just (id, e))
lift_delay e = e

lift_delay1 ctor e1    = lift_delay' (\ [e1'     ] -> ctor e1'    ) [e1    ]
lift_delay2 ctor e1 e2 = lift_delay' (\ [e1', e2'] -> ctor e1' e2') [e1, e2]
lift_delay' :: ([Expr] -> Expr) -> [Expr] -> Expr
lift_delay' ctor subexprs@(_:_) | Just subexprs' <- mapM dethunk subexprs
                  , (_, (name, (args, rtyp))) <- head subexprs' =
  Eletrec [(name, Function args rtyp (ctor (map fst subexprs')))]
    (Eatom (Avar name (Ffun (map snd args) rtyp)))
lift_delay' ctor subexprs = ctor subexprs

dethunk :: Expr -> Maybe (Expr, (Id, ([(Id, Ftyp)], Ftyp)))
dethunk (Eletrec [(i, Function args rtype body)] (Eatom (Avar i' _)))
  | i == i', all ((==Funit).snd) args
  = Just (body, (i, (args, rtype)))
dethunk _ = Nothing

{------------------------------------------------------------------------

constant folding -- the front end produces a lot of "fromLiteral" for
                 -- unsigneds which can be constant-folded away...

  I'm sure there are more to be done...
------------------------------------------------------------------------}

const_fold_atom :: Atom -> Atom
const_fold_atom (Abinop op lhs rhs) = const_fold_atom' op lhs rhs
const_fold_atom a = a

const_fold_atom' :: Binary_operation -> Atom -> Atom -> Atom
const_fold_atom' Oor (Aconst (Ointconst 0)) rhs = rhs
const_fold_atom' Oor lhs (Aconst (Ointconst 0)) = lhs
const_fold_atom' Oand (Aconst (Ointconst (-1))) rhs = rhs
const_fold_atom' Oand lhs (Aconst (Ointconst (-1))) = lhs
const_fold_atom' Oand (Aconst (Ointconst 0)) _ = Aconst (Ointconst 0)
const_fold_atom' Oand _ (Aconst (Ointconst 0)) = Aconst (Ointconst 0)
const_fold_atom' Oshl (Aconst (Ointconst 0)) _ = Aconst (Ointconst 0)
const_fold_atom' Oshl  lhs (Aunop (Omodix q) (Aconst (Ointconst p))) | p `mod` q == 0 = lhs
const_fold_atom' Oshr  lhs (Aunop (Omodix q) (Aconst (Ointconst p))) | p `mod` q == 0 = lhs
const_fold_atom' Oshru lhs (Aunop (Omodix q) (Aconst (Ointconst p))) | p `mod` q == 0 = lhs
-- danger, this is mod 32 arith because Machint is synonymous w/
-- Int32... this may be incorrect for other architectures...
const_fold_atom' Oand (Aconst (Ointconst l)) (Aconst (Ointconst r)) = Aconst (Ointconst $ (.&.) l r)
const_fold_atom' Oor (Aconst (Ointconst l)) (Aconst (Ointconst r))  = Aconst (Ointconst $ (.|.) l r)
const_fold_atom' Oxor (Aconst (Ointconst l)) (Aconst (Ointconst r)) = Aconst (Ointconst $ xor l r)
const_fold_atom' Oadd (Aconst (Ointconst l)) (Aconst (Ointconst r)) = Aconst (Ointconst $ (+) l r)
const_fold_atom' Osub (Aconst (Ointconst l)) (Aconst (Ointconst r)) = Aconst (Ointconst $ (-) l r)
const_fold_atom' Omul (Aconst (Ointconst l)) (Aconst (Ointconst r)) = Aconst (Ointconst $ (*) l r)
const_fold_atom' Oshl (Aconst (Ointconst l)) (Aunop (Omodix modV) (Aconst (Ointconst r))) = let r' = r `mod` modV in Aconst (Ointconst $ l * (2^r'))

-- not sure this is correct choice for boolean true...
const_fold_atom' (Ocmp Ceq) (Aconst (Ointconst i1)) (Aconst (Ointconst i2)) =
  Aconst (Ointconst (if i1 == i2 then 1 else 0))

-- seen in prioset example...
const_fold_atom' (Ocmp Ceq) (Abinop Oand l (Aconst (Ointconst 1))) (Aconst (Ointconst 1)) = (Abinop Oand l (Aconst (Ointconst 1)))
const_fold_atom' (Ocmp Ceq) (Abinop Oand l (Aconst (Ointconst 1))) (Aconst (Ointconst 0)) = (Aunop Onotbool (Abinop Oand l (Aconst (Ointconst 1)))) -- is this correct??

const_fold_atom' op l r = (Abinop op l r)

const_fold_expr :: Expr -> Expr
const_fold_expr (Eifthenelse (Aconst (Ointconst 0)) _ f) = f
const_fold_expr (Eifthenelse (Aconst (Ointconst c)) t _) | c /= 0 = t
const_fold_expr e = e

const_fold_prog :: [Id] -> Program -> PassM () Program
const_fold_prog _ = return . everywhere (mkT const_fold_expr `extT` const_fold_atom)

{------------------------------------------------------------------------

Let lifting

The basic transformation is:
    (letrec ([f (lambda (x ...)
                  (letrec ([g (lambda (y ...) ...)]) g))])
     ...)
 -> (letrec ([f (lambda (x ...)
                  (letrec ([g (lambda (y ...) (g' x ... y ...))]) g))]
             [g' (lambda (x ... y ...) ...)])
     ...)

The idea is that 'f' is inlinable and when it gets inlined
we have effectively accomplished uncurrying without a more complex
global optimization.

For now this transformation applies only to the top level.  To
generalize it, we need to extend implicit_args and avoid lifting past
bindings.

Note that in theory this transformation might be undone by inlining.

TODO: should we generalize beyond atoms?

------------------------------------------------------------------------}

let_lift_prog :: [Id] -> Pass () Program Program
let_lift_prog _ (Program globals functions main init types areas structs) = do
  functions' <- mapM f functions
  return (Program globals (concat functions') main init types areas structs)
  where f (x, Internal (Function args ret_typ body)) = do
          (body', new_functions) <- let_lift args body
          return $ (x, Internal (Function args ret_typ body')) :
                   [(g, Internal g') | (g, g') <- new_functions]
        f x = return [x]

let_lift :: [(Id,Ftyp)] -> Expr -> PassM () (Expr, [(Id, Function)])
let_lift implicit_args (Eletrec [(f, Function explicit_args ret_typ body)] (Eatom (Avar ref f_typ)))
  | f == ref = do
  let all_args = implicit_args ++ explicit_args
  (body', new_functions) <- let_lift all_args body
  f' <- fresh f
  explicit_arg_names' <- mapM (fresh . fst) explicit_args
  let explicit_args' = [(x, t) | ((_, t), x) <- zip explicit_args explicit_arg_names']
  ret_var <- fresh "r"
  return ((Eletrec [(f', Function explicit_args' ret_typ
                         (Elet ret_var ret_typ (Scall (Fsignature (map snd all_args) ret_typ)
                                                f (map (uncurry Avar) (implicit_args ++ explicit_args')))
                                          (Eatom (Avar ret_var ret_typ))))]
           (Eatom (Avar f' f_typ))),
          (f, Function all_args ret_typ body') : new_functions)
let_lift _ e = return (e, [])

{------------------------------------------------------------------------

Inlining

There are three sorts of things to be inlined: atoms, labels, and
functions (whether top level or not).  By inlining labels we subsume
the 'straightening' optimization that we had earlier.

While doing inlining we dynamically keep track of the binding for each
variable, the number of referenced to each variable, and a list of
functions that should be excluded from inlining (because we are in the
process of inlining that function's body).  Aside from the
complications introduced by keeping track of those, the inlining
algorithm is entirely straightforward and standard.

------------------------------------------------------------------------}

type M = ReaderT (Env, Uninlineable) (PassM Counts)
data Binding
  = LabelBinding Function Uninlineable
  | FunctionBinding Function
  | AtomBinding Atom
type Env = M.Map Id Binding

update_fst f (a, b) = (f a, b)
update_snd f (a, b) = (a, f b)

----------------
-- Counts:
--  "count_ref_in_foo (+) x" and "count_ref_in_foo (-) x" respectively
--  add or subtract one to/from the count for each ref in x

type Counts = M.Map Id Int
count_ref_in_function f e@(Function _ _ e') = count_ref_in_expr f e' >> return e
count_ref_in_bindings f e = mapM_ (count_ref_in_function f . snd) e >> return e
count_ref_in_label f l = modify (M.insertWith (flip f) l 1) >> return l

count_ref_in_atom f a = modify f' >> return a where
  f' = M.unionWith (flip f)
       (everything (M.unionWith (+)) (mkQ M.empty count_ref_in_atom') a)

count_ref_in_expr :: (Int -> Int -> Int) -> Expr -> M Expr
count_ref_in_expr f e = modify f' >> return e where
  f' = M.unionWith (flip f) $
       M.unionWith (+)
          (everything (M.unionWith (+)) (mkQ M.empty gE) e)
          (everything (M.unionWith (+)) (mkQ M.empty count_ref_in_atom') e)
  gE (Egoto l _ _) = M.singleton l 1
  gE (Elet _ _ (Scall _ l _) _) = M.singleton l 1
  gE _ = M.empty

count_ref_in_atom' :: Atom -> M.Map Id Int
count_ref_in_atom' (Agvar l _) = M.singleton l 1
count_ref_in_atom' (Avar l _) = M.singleton l 1
count_ref_in_atom' _ = M.empty

----------------
-- Uninlineable

-- | When we inline a label, the set of functions that we are in the process of inlining
-- and thus the set of functions that we should no longer inline should be taken
-- from the original is stored in the 'Uninlineable' set.
--
-- 'Nothing' means everything is uninlineable (i.e. function inlining is disabled).
-- We use this when doing certain optimization pre-passes.
type Uninlineable = Maybe (M.Map Id ())
uninlineable_insert _ Nothing = Nothing
uninlineable_insert id (Just m) = Just (M.insert id () m)
is_uninlineable id Nothing = True
is_uninlineable id (Just m) = M.member id m

-----------------
-- Inlining

-- NOTE: the monadic action for each argument should add any counts that are needed
add_bindings :: ([(Id, a)] -> body -> body) -> [(Id, M a)] -> body -> M body
add_bindings ctor bindings body = do
  counts <- get
  let isRefed counts (f,_) = M.findWithDefault 0 f counts > 0
  case partition (isRefed counts) bindings of
    ([], _) -> return body
    (refed, unrefed) -> do
      refed' <- mapM (\(id,m) -> m >>= return . (id,)) refed
      add_bindings ctor unrefed (ctor refed' body)

inline_prog' roots e = initial M.empty (\p -> runReaderT (inline_prog roots p) (M.empty, Just M.empty)) e

inline_prog :: [Id] -> Program -> M Program
inline_prog roots p@(Program globals functions main init types areas structs) = do
  let count_global (_, Global _ e) = count_ref_in_expr (+) e
      count_fundec f (_, External _) = return ()
      count_fundec f (_, Internal g) = count_ref_in_function f g >> return ()
  mapM_ count_global globals
  mapM_ (count_fundec (+)) functions
  inlineable_bindings <- inlineable_toplevels functions
  mapM_ (count_fundec (-)) functions
  mapM_ (count_ref_in_atom (+) . (flip Avar (Funit{-dummy value-}))) (nub (main : init : roots))
    -- ^ Account for the external reference
  functions' <-
    local (update_fst (M.union (M.fromList inlineable_bindings))) $
    add_bindings (++) [(l, inline_toplevel l f) | (l, f) <- functions] []
  -- TODO: run inlining over globals
  -- TODO: add globals to inlineable bindings
  -- TODO: omit globals that are not referenced
  return (Program globals functions' main init types areas structs)

inline_toplevel _ t@(External _) = return t
inline_toplevel id (Internal f) =
  liftM Internal $ inline_function id =<< count_ref_in_function (+) f

inline_function id (Function args ty body) =
  local (update_snd (uninlineable_insert id)) $
    liftM (Function args ty) (inline_expr body)

inline_atom :: Atom -> M Atom
inline_atom atom = everywhereM' (mkM f) atom where
  f :: Atom -> M Atom
  f a = do
    (env, _) <- ask
    case a of
      (Avar l _) | Just (AtomBinding atom') <- M.lookup l env ->
        count_ref_in_atom (-) a >> count_ref_in_atom (+) atom'
        -- technically we should install the env from atom', but it happen to be unnecessary
      _ -> return a

inline_binding (l, Function args ret body) =
  local (update_snd (uninlineable_insert l)) $
    liftM ((l,) . Function args ret) (inline_expr body)

inline_expr :: Expr -> M Expr
inline_expr (Eatom atom) = liftM Eatom $ inline_atom atom
inline_expr e@(Egoto label actuals ret_typ) = do
  (env, uninlineables) <- ask
  actuals' <- mapM inline_atom actuals
  case M.lookup label env of
    Nothing -> return (Egoto label actuals' ret_typ)
    -- NOTE: we don't reset the env b/c the things in-scope in the body
    -- of label_body are still in scope
    Just (LabelBinding (Function formals _ label_body) uninlineable) -> do
      count_ref_in_label (-) label
      mapM_ (count_ref_in_atom (-)) actuals'
      e' <- count_ref_in_expr (+) =<< lift (freshen_expr label_body)
      local (update_fst (M.union bindings) . update_snd (const uninlineable))
        (inline_expr e')
      where bindings = M.fromList [(fst formal, AtomBinding actual)
                                   | formal <- formals | actual <- actuals']
inline_expr (Elet id ftyp simplExpr body) = do
  simplExpr' <- runSomewhereM (somewhere (const mzero `extM` (lift . inline_atom))) simplExpr
  (env, uninlineables) <- ask
  let inline_call ctor func_id actuals = do
        mapM_ (count_ref_in_atom (-)) actuals
        case if is_uninlineable func_id uninlineables
             then Nothing
             else M.lookup func_id env of
          Nothing -> do
            body' <- inline_expr body
            --TODO: identify "pure" calls which we can omit and then use code like:
            --  add_bindings (\ [(id,a)] -> Elet id ftyp (ctor a)) [(id, mapM (inline_atom <=< count_ref_in_atom (+)) actuals)] body'
            actuals' <- mapM (inline_atom <=< count_ref_in_atom (+)) actuals
            return (Elet id ftyp (ctor actuals') body')
          Just (FunctionBinding (Function formals _ func_body)) -> do
            count_ref_in_label (-) func_id
            label <- fresh "join"
            let resTy = type_of_expr body -- TODO: we can remove this if the monad kept track of the expected type
            func_body' <- count_ref_in_expr (+) =<< freshen_expr_and_retail label resTy func_body
            local (update_fst (M.union arg_bindings))
              (inline_letlabel (uninlineable_insert func_id)
                [(label, Function [(id, ftyp)] resTy body)] func_body')
            where arg_bindings = M.fromList [(fst formal, AtomBinding actual)
                                           | formal <- formals | actual <- actuals]
      inline_atom_ref atom = do
        count_ref_in_atom (-) atom
        counts <- get
        if inlineable_atom counts id atom
        then local (update_fst (M.insert id (AtomBinding atom))) (inline_expr body)
        else do count_ref_in_atom (+) atom
                liftM (Elet id ftyp (Satom atom)) (inline_expr body)
  case simplExpr' of
    -- TODO: We could avoid the extra retail pass if we kept count of the number of branches in each bit of code
    Scall fsignature func_id actuals -> inline_call (Scall fsignature func_id) func_id actuals
    Sapp fsignature (Avar id t) actuals -> inline_call (Sapp fsignature (Avar id t)) id actuals
    Satom atom -> inline_atom_ref atom
    e@(Salloc tcon nat atoms) -> liftM (Elet id ftyp e) (inline_expr body)
    e@(Sapp fsignature func_atom actuals) -> liftM (Elet id ftyp e) (inline_expr body)
inline_expr (Eletrec bindings body) = do
  -- NOTE: we have to disable function inlining when simplifying the rhs b/c otherwise
  -- we would loose track of what code came from an inlining and we could get in an infinite
  -- loop of inlining expansions.  When a rhs does get inlined somewhere, however,
  -- the inlining still operates over the body.
  inlineable_bindings <- inlineable_funcs bindings
  bindings' <- local (update_fst (M.union (M.fromList inlineable_bindings)) .
                      update_snd (const Nothing)) (mapM inline_binding bindings)
  inlineable_bindings' <- inlineable_funcs bindings'
  count_ref_in_bindings (-) bindings'
  body' <- local (update_fst (M.union (M.fromList inlineable_bindings'))) (inline_expr body)
  add_bindings Eletrec [(l, inline_function l =<< count_ref_in_function (+) r)
                       | (l,r) <- bindings'] body'
inline_expr (Eletlabel bindings body) = inline_letlabel id bindings body
inline_expr e = gmapM (runSomewhereM (somewhere
                                        (const mzero `extM`
                                         (return :: Id -> ExceptT String M Id) `extM`
                                         (return :: Ftyp -> ExceptT String M Ftyp) `extM`
                                         (lift . inline_expr) `extM`
                                         (lift . inline_atom)))) e

-- We have this factored out because while the code for inlining a
-- regular Eletlabel and inlining an Eletlabel introduced by the
-- inlining of a function call are almost identical they differ in the
-- uninlineables that go on the body of the Eletlabel.
inline_letlabel modify_uninlineable bindings body = do
  inlineable_bindings <- inlineable_labels bindings
  bindings' <- local (update_fst (M.union (M.fromList inlineable_bindings)) .
                      update_snd (const Nothing)) (mapM inline_binding bindings)
  -- ^ TODO: Do we really need to disable inlining here?
  inlineable_bindings' <- inlineable_labels bindings'
  count_ref_in_bindings (-) bindings'
  body' <- local (update_fst (M.union (M.fromList inlineable_bindings')) .
                  update_snd modify_uninlineable) (inline_expr body)
  add_bindings Eletlabel [(l, inline_function l =<< count_ref_in_function (+) r)
                         | (l,r) <- bindings'] body'

---------------
-- Inlineability:
--  'inlineable_foos' takes a list of 'foo' and returns the list of bindings of 'foo'
--     that are considered inlineable.
--  'inlineable_foo' takes a 'foo' and returns True if it should be considered inlineable.

--------
-- Atoms
inlineable_atom counts l (Agvar _ _) = True
inlineable_atom counts l (Avar _ _) = True
inlineable_atom counts l (Aconst _) = True
inlineable_atom counts l (Aunop _ _) | M.findWithDefault 0 l counts <= 1 = True
inlineable_atom counts l (Abinop _ _ _) | M.findWithDefault 0 l counts <= 1 = True
inlineable_atom counts l a | atom_depth a <= 3 = True
inlineable_atom counts l _ = False

--------
-- Labels
inlineable_labels ls = do
  counts <- get
  uninlineable <- reader snd
  return [(l, LabelBinding f ({-uninlineable_insert l-} uninlineable))
         | (l, f) <- ls, inlineable_label counts (l, f)]

inlineable_label counts (_, Function _ _ (Eatom (Agvar _ _))) = True
inlineable_label counts (_, Function _ _ (Eatom (Avar _ _))) = True
inlineable_label counts (_, Function _ _ (Eatom (Aconst _))) = True
inlineable_label counts (_, Function _ _ (Egoto _ _ _)) = True
inlineable_label counts (_, Function _ _ (Elet _ _ (Sapp _ _ _) (Eatom _))) = True
inlineable_label counts (l, _) | M.findWithDefault 0 l counts <= 1 = True
inlineable_label counts _ = False

--------
-- Top-level functions
inlineable_toplevels toplevels = do
  counts <- get
  return [(l, FunctionBinding f) |
          (l, Internal f) <- toplevels,
          inlineable_toplevel counts l f]

-- TODO: harmonize inlineable_func with inlineable_toplevel
-- TODO: does expr_depth subsume atom_depth?
-- TODO: should expr_depth add atom_depth to its count?
-- TODO: does expr_depth apply to internal functions and does it subsume the manual tests there?
inlineable_toplevel counts label f@(Function _ _ body)
--  | M.findWithDefault 0 label counts <= 1 = True
  | Eatom a <- body, atom_depth a <= 3 = True
  | expr_depth body <= 3 = True -- TODO: 3 -> 4???
  | Function _ _
    (Eletrec [(_, Function _ _ (Elet _ _ (Scall _ _ _) (Eatom (Avar _ _))))] (Eatom (Avar _ _))) <- f = True -- Inline 'let_lift'ed functions
  | otherwise = False --inlineable_func counts (label, f)

-- Andrew S-W's code took the max depth
-- and we are taking the total size.  I'm not sure how much
-- difference it makes.
atom_depth :: Atom -> Int
atom_depth a = everything (+) (mkQ 0 (const 1 :: Atom -> Int)) a

expr_depth :: Expr -> Int
expr_depth e = everything (+) (mkQ 0 (const 1 :: Expr -> Int)) e

--------
-- Non-top-level functions

inlineable_funcs fs = do
  counts <- get
  return [(l, FunctionBinding f) | (l, f) <- fs, inlineable_func counts (l, f)]

inlineable_func counts (_, Function _ _ (Eatom (Agvar _ _))) = True
inlineable_func counts (_, Function _ _ (Eatom (Avar _ _))) = True
inlineable_func counts (_, Function _ _ (Eatom (Aconst _))) = True
inlineable_func counts (_, Function _ _ (Egoto _ _ _)) = error "INTERNAL ERROR: Goto as body of function" -- Should never happen
inlineable_func counts (_, Function _ _ (Elet _ _ (Sapp _ _ _) (Eatom _))) = True
inlineable_func counts (l, _) | M.findWithDefault 0 l counts <= 1 = True
inlineable_func counts _ = False

------------------------
-- Freshen and retail
------------------------

-- TODO: fuse these passes?
freshen_expr_and_retail l t e = liftM (retail l t) (lift (freshen_expr e))

-- Note that we do not retail 'Function's so we don't retail the rhs of 'letrec' or 'let'
retail :: Label -> Ftyp -> Expr -> Expr
retail k t (Eletrec fs body) = Eletrec fs (retail k t body)
retail k t (Eletlabel labels let_body) = Eletlabel (map f labels) (retail k t let_body)
  -- We have to update the return type of labels and gotos
  where f (l, Function args _ label_body) = (l, Function args t (retail k t label_body))
retail k t (Egoto l args _) = Egoto l args t
retail k t (Eerror _) = Eerror t
retail k t (Eatom a) = Egoto k [a] t
retail k t e = gmapT (runSomewhere (somewhere (const Nothing `extM` (Just . retail k t)))) e

freshen_expr :: Expr -> PassM st Expr
freshen_expr e = liftM fst $ localState freshen_expr' M.empty e where
  freshen_expr' :: Expr -> PassM (M.Map Id Id) Expr
  freshen_expr' = everywhereButM' (const False `extQ`
                                     (const True :: Ftyp -> Bool) `extQ`
                                     (const True :: String -> Bool))
                  (mkM do_expr `extM` do_id `extM` do_func)
  do_expr e = freshen_ids (ids_of_expr e) >> return e
  do_func e@(Function args _ _) = freshen_ids (map fst args) >> return e
  -- TODO: factor out alts (and def?) of case?
  freshen_ids :: [Id] -> PassM (M.Map Id Id) ()
  freshen_ids ids = do
    ids' <- mapM fresh ids
    modify (M.union (M.fromList (zip ids ids'))) -- M.union is biased towards/prefers the left
  do_id :: Id -> PassM (M.Map Id Id) Id
  do_id id = do
    subst <- get
    case M.lookup id subst of
      Just id' -> return id'
      Nothing -> return id
  ids_of_expr :: Expr -> [Id]
  ids_of_expr (Eatom _) = []
  ids_of_expr (Elet id _ _ _) = [id]
  ids_of_expr (Eletrec fs _) = map fst fs
  ids_of_expr (Eifthenelse _ _ _) = []
  ids_of_expr (Ecase _ alts Nothing) = map (\(id,_,_) -> id) alts
  ids_of_expr (Ecase _ alts (Just (def, _))) = def : map (\(id,_,_) -> id) alts
  ids_of_expr (Eixcase _ _ id _ _) = [id]
  ids_of_expr (Enzcase _   id _ _) = [id]
  ids_of_expr (Erefcase _ _ id _ _) = [id]
  ids_of_expr (Eerror _) = []
  ids_of_expr (Eletlabel fs _) = map fst fs
  ids_of_expr (Egoto _ _ _) = []
