requires prelude

foo :: Bit 8 -> Bit 12
foo ((x :: Bit 6) :# y) = x :# x

upper (x :# y) = x

upper6 :: Bit 12 -> Bit 6
upper6 = upper

bar ((x :: Bit 6) :# y) = x :# x

baz (x :# y) = f x :# y
  where f :: Bit 4 -> Bit 4
        f x = x
