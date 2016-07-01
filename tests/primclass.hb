primitive type Bit (n :: nat)
primitive bits :: Bit n

primitive class (+) (a :: nat) (b :: nat) (c :: nat) | a b -> c, a c -> b, b c -> a

g :: Bit n -> Bit m -> Bit (n + m)
g x y = bits

q :: Bit 4
q = bits

r :: Bit 5
r = bits

s = g q r


{- Things that should fail:

data Maybe t = Just t | Nothing

h :: Bit n -> Maybe n
h x = h x

instance Maybe m + Maybe n = Maybe (m + n)

-}