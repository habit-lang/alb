--------------------------------------------------------------------------------
-- Quill prelude
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Primitive types and classes: functions and linearity

primitive type (-*>) :: * -> * -> *
primitive type (-!>) :: * -> * -> *
class (->) (f :: * -> * -> *)
infixr type 5 -*>, -!>, ->

instance (->) (-!>)
else (->) (-*>)
else (->) t fails

class t >:= u
instance t >:= u fails if Un t fails, Un u
else t >:= u

class Un t
instance Un (-!>)
instance Un ((-!>) t)
instance Un (t -!> u)

instance Un (-*>) fails
instance Un ((-*>) t) fails
instance Un (t -*> u) fails

class ShFun t

class SeFun t
instance SeFun (-!>) fails
instance SeFun ((-!>) t) fails
instance SeFun (t -!> u) fails

--------------------------------------------------------------------------------
-- Standard types and classes

data Pair a b = P a b

inl (P a b) = a
inr (P a b) = b

data Unit = Unit

data Bool = False | True

otherwise :: Bool
otherwise = True

not :: Bool -!> Bool
not True = False
not False = True

data Ordering = LT | EQ | GT

class Eq t where
  (==), (/=) :: (t >:= f t Bool) => t -!> t ->{f} Bool
  x /= y      = not (x == y)   -- default definition

class Ord t | Eq t where
  compare              :: (t >:= f t Ordering) => t -!> t ->{f} Ordering
  (<), (<=), (>), (>=) :: (t >:= f t Bool) => t -!> t ->{f} Bool
  min, max             :: Un t => t -!> t -!> t

  x <= y  = case compare x y of GT -> False; _ -> True
  x <  y  = case compare x y of LT -> True;  _ -> False
  x >= y  = case compare x y of LT -> False; _ -> True
  x >  y  = case compare x y of GT -> True;  _ -> False

  min x y = case x <= y of True -> x; False -> y
  max x y = case y <= x of True -> x; False -> y

--  compare x y = case x == y of
--                  True  -> EQ
--                  False -> case x <= y of
--                             True  -> LT
--                             False -> GT

class Bounded t where
  minBound, maxBound :: t

-- Some fancy types

-- const :: (Un b, a >:= (b ->{f} a), a >:= (b ->{g} a)) => a ->{f} b ->{g} a
-- const a b = a

class Functor f m | m -> f where
      fmap :: {- what should be the predicates here? -} (a -> b) ->{f} m a ->{g} m b


class Applicative f m | m -> f where
      pure :: {- what should be the predicates here? -} t -> m t
      (<$>) :: {- what should be the predicates here? -} m (a -> b) -> m a -> m b


class Monad f m | m -> f where
      return :: (t >:= m t) => t -> m t
      -- [ANI] TODO we need to give too many details here
      -- can we reduce the constraints to only (m t >:= g, f >:= m u)
      (>>=)  :: (m t >:= ((t ->{f} m u) ->{g} m u), f >:= m u) =>
                m t -> (t ->{f} m u) ->{g} m u

data Maybe a = Nothing | Just a
     -- deriving Show ??

instance Monad (-!>) Maybe where
         return a = Just a
         (>>=) Nothing f = Nothing
         (>>=) (Just a) f = f a


-- Some simple examples using \*x and \&x

f' :: (Un a, SeFun f) => a ->{f} Pair a a
f' = \*x -> P x x

f'' = \*x -> \*y -> \*z -> P x z

g :: (Un a, ShFun f) => a ->{f} Pair a a
g = \&y -> P y y
