class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *


-- Examples taken from Jones's FC Polymorphism 
-- id :: a -> a
-- id = \x -> x

-- data Boolean = True | False
-- data Either a b = L a | R b

data Boolean = (forall a) B (a -> a -> a)

tr :: a -> a -> a
-- tr = \t -> \f -> t
tr t f = t

-- true   :: Boolean
-- true   =  B tr 
-- false  :: Boolean
-- false  =  B (\_ -> \f -> f)  

-- cond     :: Boolean -> a -> a -> a
-- cond (B b) = b

-- and , or  :: Boolean -> Boolean -> Boolean
-- and x y = cond x y false
-- or x y = cond x y true
