requires prelude
-- class (@) (t :: k' -> k) (u :: k')

-- primitive type (->) :: * -> * -> *
-- infixr type 5 ->

-- Pierce and Turner Object calculus (essentially F_omega with subtyping)

-- data Point = (forall r) MkPt r                     -- state
--                              (r -> Unsigned -> r)  -- set state
--                              (r -> Unsigned)       -- get state

-- class PointM r where
--    bump :: (r -> r)
--    setX :: (r -> Unsigned -> r)
--    getX :: (r -> Unsigned)

data Obj m = (exists s) (if m @ s) MkObj s       -- state
                                         (m s)   -- method


data Class m n = (forall f) MkClass ((f -> n)              -- extract
                                ->  (f -> n -> f)         -- overwrite
                                ->  m f                   -- self 
                                ->  m f )

new :: (m @ s) => Class m s -> s -> Obj m
new (MkClass c) s = MkObj s m'
                -- c:: (f -> n) -> (f -> n -> f) -> (m f) -> (m f) 
       where m' = c (\r -> r) (\_ r -> r) m'


-- Natural transformations:
-- data NT m n = (forall a) (if m @ a, n @ a) MkNT (m a -> n a)

-- coerce :: NT m n -> (m a -> n a)
-- coerce (MkNT t) = t

-- data PointM s = MkP (s -> Unsigned -> s) (s -> Unsigned)

-- set :: PointM s -> (s -> Unsigned -> s)
-- set (MkP s g) = s

-- get :: PointM s -> (s -> Unsigned)
-- get (MkP s g) = g

-- pointSet' :: NT p PointM -> (Obj p -> Unsigned -> Obj p)
-- pointSet' st (MkObj s m) i
--   = MkObj (set (coerce st m) s i) m

-- pointClass :: Class PointM Unsigned
-- pointClass = MkClass (\extr over _ -> MkP (\r i -> over r i) (\r -> extr r))

-- Inheritance:
-- data Inc s n r
--   = (forall f) MkInc ((f -> r)        -- extract
--                    -> (f -> r -> f)   -- overwrite
--                    -> s f             -- super methods
--                    -> n f             -- self methods
--                    -> n f)            -- new methods


{-
Context too weak to prove:
    (@) q s$1 arising at tests/fc-poly/class.hb:7:34-39
    (@) p s$1 arising at tests/fc-poly/class.hb:53:25-54:22
Note: the type variable s$1 is ambiguous.
    In the explicit binding for ext :: NT p q ->
                                       Class q s ->
                                       Inc q p r -> (r -> s) -> (r -> s -> r) -> Class p r

-}
-- ext :: NT p q
--     -> Class q s         -- super
--     -> Inc q p r         -- increment
--     -> (r -> s)          -- extract
--     -> (r -> s -> r)     -- overwrite
--     -> Class p r         -- new class
-- ext st (MkClass sup) (MkInc inc) gt pt
--   = MkClass (\g p self ->
--                 inc g p (sup (\s -> gt (g s))
--                         (\s t -> p s (pt (g s) t))
--                         (coerce st self))
--               self)
