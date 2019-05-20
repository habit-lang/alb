-- requires base

class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *
infixr type 5 ->

-- primitive undefined :: a

data Switch = On | Off
data Prop = T | F | U

silly' :: Prop -> Prop -> Prop
silly' a b = a

silly :: Switch -> Switch -> Switch
silly a b = a

-- Examples taken from Jones's FC Polymorphism 
data Boolean = (forall a) B (a -> a -> a)
-- B :: (forall a. a -> a -> a) -> Boolean
-- currently it treats it as forall a. (a -> a -> a -> Boolean)

cond      :: Boolean -> a -> a -> a
cond (B b) = b

--- does a less polymorphic function work? ---
-- This works but shouldn't
sillyB :: Boolean
sillyB = B silly

-- sillyP :: Boolean
-- sillyP = B silly'

-- t :: a -> a -> a
-- t x y = x

tr   :: Boolean
tr   =  B (\t -> \_ -> t)
fl :: Boolean
fl  =  B (\_ -> \f -> f)  


-- and, or  :: Boolean -> Boolean -> Boolean
-- and x y = cond x y fl
-- or x y = cond x y tr
