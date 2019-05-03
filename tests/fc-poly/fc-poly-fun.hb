class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *

data T a = MkT (a -> a)

data D1 = (forall a) MkD1 (a -> a -> a)

data D2 = (forall a, b, c) MkD2 (a -> b -> c) 

{-
data T a = (forall b) MkT1 (b -> b)
         | (forall c) MkT2 (c -> a)
         | (forall d) MkT3 (d a -> a)
         | (forall e, f) MkT4 (e f -> a)
-}