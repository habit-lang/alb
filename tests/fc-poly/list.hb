class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *

data List a = (forall b) L ((a -> b -> b) -> b -> b)
