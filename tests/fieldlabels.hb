requires prelude

data Foo = Foo[cake :: Foo | isFrosty :: Bool]
         | Bar Unsigned

foo = Foo[isFrosty = True | cake = Foo[isFrosty = False | cake = Foo (Bar 1) False]]

bar Foo[isFrosty = x | cake = Foo[cake = Foo y z]] =
  Foo[isFrosty = x && z | cake = y]