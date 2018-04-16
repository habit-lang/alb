requires qprelude

-- Standard types and classes

-- data Unit = Unit
-- instance Un Unit

data Bool = False | True
instance Un Bool

-- otherwise :: Bool
-- otherwise = True

-- not :: Bool -> Bool
-- not True = False
-- not False = True

-- data Ordering = LT | EQ | GT
-- instance Un Ordering

data Choice a b = L a | R b
data Pair a b = P a b

data Pair' a b = ShP !! a b

-- ctob :: (->) f => f (Choice a b) -> Bool
-- ctob x = {( L a <- x => ^False | R b <- x => ^False )}
--              g => commit False | g => commit False

-- ctob :: Choice Bool Bool -> Bool
-- ctob (L x) = x
-- ctob (R y) = y

-- ctob' :: {- (Un a, Un b, SeFun f) =>-} Choice a b ->{f} Pair' (Choice a b) Bool
-- ctob' (L x) = P (L x) True
-- ctob' (R y) = P (R y) False

-- fstp :: Pair' a b -> a
fstp (ShP a b) = a

-- swap :: (SeFun f) => Pair a b ->{f} Pair b a
-- swap (P a b) = P b a

-- fst :: (Un b) => Pair a b -> a
-- fst (P a b) = a

-- snd :: (Un a) => Pair a b -> b
-- snd (P a b) = b

-- class Eq t where
--   (==) :: (t >:= f t Bool) => t -> t ->{f} Bool
--   (/=) :: (t >:= f t Bool) => t -> t ->{f} Bool
--   x /= y      = not (x == y)   -- default definition

-- class Ord t | Eq t where
--   compare              :: (t >:= f t Ordering) => t -> t ->{f} Ordering
--   (<), (<=), (>), (>=) :: (t >:= f t Bool) => t -> t ->{f} Bool
--   min, max             :: Un t => t -!> t -!> t

--   x <= y  = case compare x y of GT -> False; _ -> True
--   x <  y  = case compare x y of LT -> True;  _ -> False
--   x >= y  = case compare x y of LT -> False; _ -> True
--   x >  y  = case compare x y of GT -> True;  _ -> False

--   min x y = case x <= y of True -> x; False -> y
--   max x y = case y <= x of True -> x; False -> y

--  compare x y = case x == y of
--                  True  -> EQ
--                  False -> case x <= y of
--                             True  -> LT
--                             False -> GT

-- class Bounded t where
--   minBound, maxBound :: t

-- Some fancy types

-- const :: (Un b, a >:= (b ->{f} a), a >:= (b ->{g} a)) => a ->{f} b ->{g} a
-- const a b = a

-- class Functor f m | m -> f where
--       fmap :: {- what should be the predicates here? -} (a -> b) ->{f1} m a ->{g1} m b


-- class Applicative f m | m -> f where
--       pure :: {- what should be the predicates here? -} t -> m t
--       (<$>) :: {- what should be the predicates here? -} m (a -> b) ->{f1} m a ->{g1} m b


-- class Monad f m | m -> f where
--       return :: (t >:= m t) => t -> m t
--       -- [ANI] TODO we need to give too many details here
--       -- can we reduce the constraints to only (m t >:= g, f >:= m u)
--       (>>=)  :: (m t >:= ((t ->{f} m u) ->{g} m u), f >:= m u, ShFun f) =>
--                 m t -> (t ->{f} m u) ->{g} m u

-- data Maybe a = Nothing | Just a
--      -- deriving Show ??

-- instance Monad (-!>) Maybe where
--          -- return :: a -> Maybe a
--          return a = Just a
--          -- we cannot have a linear funtion f here as it is not used exactly once.
--          -- (>>=) :: m a -> (a -> m b) -> m b
--          (>>=) Nothing f = Nothing
--          (>>=) (Just a) f = f a