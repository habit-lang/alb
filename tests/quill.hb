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

--------------------------------------------------------------------------------
-- Standard types and classes

data Pair a b = P a b

inl (P a b) = a
inr (P a b) = b

data Unit = Unit

data Bool = False | True

otherwise = True

not :: Bool -!> Bool
not True = False
not False = True

data Ordering = LT | EQ | GT

class Eq t where
  (==) :: (t >:= f t Bool) => t -!> t ->{f} Bool
  (/=) :: (t >:= f t Bool) => t -!> t ->{f} Bool
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


-- Some simple examples using \*x and \&x

f' :: (Un a) => a -> Pair a a
f' = \*x -> P x x

-- f :: a -> Pair a a
-- f = \&y -> P y y -- This should not typecheck but should be parsed