requires prelude

bitdata Foo = Foo [ x = 0 :: Unsigned ]
            | Bar [ y :: Bit 16 | z :: Bit 16 ]

bitdata Baz = Baz  [ x :: Foo ]
            | Quux [ y :: Unsigned ]

bitdata Solo = S [ x :: Baz ]

type Nibble = Bit 8

bitdata Bozo = Bozo [ x, y :: Nibble ]

x = Foo []
v = Foo
--w = Bar []
z = Bar [y = 0 | z = 0]
y = Foo [x = 0]


f x = case x of
        Foo [x] -> Foo [x = x + 1]
        Bar [y = a | z = b] -> Bar [y = a | z = a + b]

g x = case x of
        Foo r -> Foo [x = r.x + 1]
        Bar r -> Bar [y = r.y | z = r.y + r.z]
