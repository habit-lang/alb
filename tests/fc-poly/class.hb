-- Partial data types: ------------------------------------------
class (@) (t :: k' -> k) (u :: k')

-- Basic types: -------------------------------------------------
primitive type (->) :: * -> * -> *
infixr type 5 ->

-- Pierce and Turner Object calculus with classes
data Obj m = (forall s) MkObj s       -- state
                              (m s)   -- method
                              if m @ s

data Class m s = (forall f) MkClass  ((f -> s)              -- extract
                                  -> (f -> s -> f)         -- overwrite
                                  ->  m f                   -- self 
                                  ->  m f)
                                   -- if ((->) (a -> a)) @ ((->) ((->) a (a -> a)) ((b a) -> (b a)))
                                   -- , (->) @ (a -> a)
                                   -- , ((->) a) @ a
                                   -- , (->) @ a
                                   -- , ((->) ((->) a ((->) a a))) @ ((->) (b a) (b a))
                                   -- , (->) @ (a -> (a -> a))
                                   -- , ((->) a) @ (a -> a)
                                   -- , (->) @ a
                                   -- , ((->) a) @ a
                                   -- , (b -> a) @ (b a)
                                   -- , (->) @ (b a)
                                   -- , b @ a
--                                   
-- new :: Class m s -> s -> Obj m
-- new (MkClass c) s = MkObj s m
--        where m = c (\r -> r) (\_ r -> r) m

-- Natural transformations:
-- data NT m n = MkNT { coerce :: forall a. m a -> n a }

-- data PointM s = MkP{ set :: (s -> Int -> s),
--                      get :: (s -> Int) }

-- point'Set :: NT p PointM -> (Obj p -> Int -> Obj p)
-- point'Set st (MkObj s m) i
--   = MkObj (set (coerce st m) s i) m

-- pointClass :: Class PointM Int
-- pointClass = MkClass (\extr over _ -> MkP { set = \r i -> over r i,
--                                             get = \r -> extr r })


-- Inheritance:
-- data Inc s n r
--   = MkInc (forall f. (f -> r)        -- extract
--                   -> (f -> r -> f)   -- overwrite
--                   -> s f             -- super methods
--                   -> n f             -- self methods
--                   -> n f)            -- new methods

-- ext :: NT p q
--     -> Class q s         -- super
--     -> Inc q p r         -- increment
--     -> (r -> s)          -- extract
--     -> (r -> s -> r)     -- overwrite
--     -> Class p r         -- new class
-- ext st (MkClass sup) (MkInc inc) _ put
--   = MkClass (\g p self ->
--                inc g p (sup (\s -> get (g s))
--                         (\s t -> p s (put (g s) t))
--                         (coerce st self))
--               self)
