requires miniprelude

class t == u | t -> u, u -> t

instance t == t

f :: (t == u) => t v -> u v
f x = x

g :: (t == u) => t -> u
g x = x

g' :: (f == g, t == u) => f t -> g u
g' x = x

data Q t u = Q (t u)

data T = C (Q Maybe Unsigned) | D (Q Lab #.foo)

data TheNat (n :: nat) = TheNat

h :: Q TheNat 2
h = Q TheNat

j :: Q Maybe Unsigned
j = Q Nothing

k :: (Q TheNat 2, Q Maybe Unsigned)
k = (h, j)

data Either t u = Left t | Right u

l :: Q (Either Unsigned) Unsigned
l = Q (Left 1)

m :: Q (Q Maybe) Unsigned
m = Q (Q Nothing)

-- Kind errors

-- err :: Q Unsigned Unsigned
-- err = Q 1

-- err2 :: Q Either Unsigned
-- err2 = Q (Left 1)

-- data U (t :: k) = U (t Unsigned)

-- class D (t :: k)
--    where foo :: t u -> Unsigned

class (t :: k) =:= (u :: k) | t -> u, u -> t
instance t =:= t

-- This shouldn't work
-- ff :: (t =:= u) => t v -> u -> u
-- ff x y = y

gg :: (t =:= u, v =:= w) => t v -> u w
gg x = x

data Proxy t = Proxy

-- hh :: (t == Unsigned) => Proxy (t :: k) -> Unsigned
-- hh _ = 0

-- jj :: Proxy (t :: k) -> t -> Unsigned
-- jj _ _ = 0
