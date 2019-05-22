class (@) (t :: k' -> k) (u :: k')

primitive type (->) :: * -> * -> *
infixr type 5 ->

-- Passes
-- data T a = MkT1 (a -> a)
--          | (forall b) MkT2 (b -> a)
--          | (forall c) MkT3 (c a -> a)

-- Passes
data D1 = (forall a) MkD1 (a -> a -> a)

-- FAILS due to some reason of inst ts !! TyGen int?
data D2 p = (forall a, b) MkD2 (a b -> p) 

-- Passes
data D3 a = (forall b) MkD3 ((b a) -> a)

-- Passes
data D4 p q = MkD4 (p -> q)
-- Passes
data D5 p q = (forall a) MkD5 (a -> p -> q) 

data D6 p = (forall a, b, c) MkD6 ((a -> b -> c) -> p)

-- FAILS when universal >= 1 and existentials >= 2 
data T a = (forall b) MkT1 (b -> b)
         | (forall c) MkT2 (c -> a)
        | (forall d) MkT3 (d a -> a)
        | (forall e, f) MkT4 (e f -> a)
