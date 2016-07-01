requires qprelude

class F (a :: *) (b :: *) | a -> b

data T a = MkT b if F a b

f :: T a -> T a
f (MkT b) = MkT b

g :: (F a b, F a' b) => T a -> T a'
g (MkT b) = MkT b

-- These should not typecheck:
--
-- h :: F a' b => T a -> T a'
-- h (MkT b) = MkT b
--
-- j :: T a -> T a'
-- j (MkT b) = MkT b

-- Neither should these
--
-- data U (a :: *) = C Bool
--                 | D b
--
-- bitdata B = B [ x :: t ]

data Equ a b = Refl if a == b

h z x y =
    j z x y
    (case z of
       Refl -> x < y)

j :: Equ a b -> a -> b -> c -> c
j x y z w = w