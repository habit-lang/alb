class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *
infixr type 5 ->

-- requires prelude

-- Examples taken from Jones's FC Polymorphism 

data Boolean = (forall a) B (a -> a -> a)

-- tr, fl   :: Boolean
-- tr   =  B (\t -> \_ -> t)
-- fl  =  B (\_ -> \f -> f)  

-- cond     :: Boolean -> a -> a -> a
-- cond (B b) = b

-- and, or  :: Boolean -> Boolean -> Boolean
-- and x y = cond x y fl
-- or x y = cond x y tr

--- does a less polymorphic function work? ---
data Switch = On | Off

silly :: Switch -> Switch -> Switch
silly a b = a


-- This works but shouldn't
sillyB :: Boolean
sillyB = B silly