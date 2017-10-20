
data Foo a b = MkFoo1 a
             | MkFoo2 b

data T t = MkT (u t) forall u

data SillyPair a = MkSP a List b forall b

length :: List a -> Int
length = undefined

f :: Pair Int -> Int
f (MkPair a l) = length l
