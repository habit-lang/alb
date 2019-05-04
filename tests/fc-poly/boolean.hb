class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *
infixr type 5 ->

-- Examples taken from Jones's FC Polymorphism 

data Boolean = (forall a) B (a -> a -> a)

true, false   :: Boolean
true   =  B (\t -> \f -> t)
false  =  B (\_ -> \f -> f)  

cond     :: Boolean -> a -> a -> a
cond (B b) = b

and , or  :: Boolean -> Boolean -> Boolean
and x y = cond x y false
or x y = cond x y true
