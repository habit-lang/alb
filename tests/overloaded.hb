requires miniprelude

class C t
   where f :: t -> t

g :: C t => t -> t
g x = f (f x)

h x = f (f x)

j x = j (h x)
j' x = h (j' x)

k x = k (h (k x))

class F a b | a -> b
    where q :: a -> b

primitive type (Int :: *)
primitive type (Float :: *)
primitive zero :: Float

instance F Int Bool
    where q _ = True

instance F Bool Float
    where q _ = zero

r :: (F a b, F b c) => a -> c
r x = q (q x)

s x = q (q x)

t :: Int -> Float
t = s 

class D a
   where m :: C b => a -> b

