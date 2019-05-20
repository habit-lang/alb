class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *
infixr type 5 ->

primitive undefined :: a

data Switch = On | Off
data Prop = T | F | U

silly' :: Prop -> Prop -> Prop
silly' a b = a

silly :: Switch -> Switch -> Switch
silly a b = a

compose f g = \x -> g (f x)