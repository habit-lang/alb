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

cond      :: Boolean -> a -> a -> a
cond (B b) = b

tr   :: Boolean
tr   =  B (\t -> \_ -> t)
fl :: Boolean
fl  =  B (\_ -> \f -> f)  

and, or  :: Boolean -> Boolean -> Boolean
and x y = cond x y fl
or x y = cond x y tr

id :: a -> a
id x = x

-- compose f g = \x -> f (g x)

on = id On