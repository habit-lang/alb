class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *

-- data T a = MkT1 (a -> a)
--          | (forall b) MkT2 (b -> a)

-- data D1 = (forall a) MkD1 (a -> a -> a)

-- data D2 p1 = (forall a, b, c) MkD2 ((a -> b -> c) -> p1) 

-- data D3 a = (forall b) MkD3 ((b a) -> a)

-- data T a = (forall b) MkT1 (b -> b)
--          | (forall c) MkT2 (c -> a)
--         | (forall d) MkT3 (d a -> a)
--         | (forall e, f) MkT4 (e f -> a)
