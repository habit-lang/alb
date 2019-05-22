requires prelude

-- Pierce and Turner Object calculus with classes
data Obj m = (forall s) (if m @ s) MkObj s       -- state
                                         (m s)   -- method

data Class m s = (forall f) (if m @ f) MkClass  ((f -> s)              -- extract
                                                -> (f -> s -> f)         -- overwrite
                                                ->  m f                   -- self 
                                                ->  m f)

{- FAILS!! with
Context too weak to prove:
    (@) (m :: (* -> *)) (s :: *) arising at tests/fc-poly/class.hb:7:33-38
    In the explicit binding for new :: forall (m :: * -> *) (s :: *).
                                           (Class :: ((* -> *) -> * -> *))
                                               (m :: (* -> *))
                                               (s :: *) (-> :: (* -> * -> *))
                                           (s :: *) (-> :: (* -> * -> *))
                                           (Obj :: ((* -> *) -> *)) (m :: (* -> *))
-}
-- new :: Class m s -> s -> Obj m
-- new (MkClass c) s = MkObj s m
--        where m = c (\r -> r) (\_ r -> r) m

-- Natural transformations:
data NT m n = (forall a) MkNT (m a -> n a)

coerce :: NT m n -> (m a -> n a)
coerce (MkNT t) = t

data PointM s = MkP (s -> Unsigned -> s) (s -> Unsigned)

set :: PointM s -> (s -> Unsigned -> s)
set (MkP s g) = s

get :: PointM s -> (s -> Unsigned)
get (MkP s g) = g

-- pointSet' :: NT p PointM -> (Obj p -> Unsigned -> Obj p)
-- pointSet' st (MkObj s m) i
--   = MkObj (set (coerce st m) s i) m

pointClass :: Class PointM Unsigned
pointClass = MkClass (\extr over _ -> MkP (\r i -> over r i) (\r -> extr r))


-- Inheritance:
data Inc s n r
  = (forall f) MkInc ((f -> r)        -- extract
                     -> (f -> r -> f)   -- overwrite
                     -> s f             -- super methods
                     -> n f             -- self methods
                     -> n f)            -- new methods

{- FAILS! with
Context too weak to prove:
    (@) (q :: (* -> *)) (t :: *) arising at tests/fc-poly/class.hb:7:33-38
    (@) (p :: (* -> *)) (t :: *) arising at tests/fc-poly/class.hb:43:25-44:22
Note: the type variable (t :: *) is ambiguous.
    In the explicit binding for ext :: forall (p :: * -> *) (q :: * -> *)
                                              (s :: *) (r :: *).
                                           (NT :: ((* -> *) -> (* -> *) -> *))
                                               (p :: (* -> *))
                                               (q :: (* -> *)) (-> :: (* -> * -> *))
                                           (Class :: ((* -> *) -> * -> *))
                                               (q :: (* -> *))
                                               (s :: *) (-> :: (* -> * -> *))
                                           (Inc :: ((* -> *) -> (* -> *) -> * -> *))
                                               (q :: (* -> *))
                                               (p :: (* -> *))
                                               (r :: *) (-> :: (* -> * -> *))
                                           ((r :: *) (-> :: (* -> * -> *))
                                            (s :: *)) (-> :: (* -> * -> *))
                                           ((r :: *) (-> :: (* -> * -> *))
                                            (s :: *) (-> :: (* -> * -> *))
                                            (r :: *)) (-> :: (* -> * -> *))
                                           (Class :: ((* -> *) -> * -> *)) (p :: (* -> *)) (r :: *)

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