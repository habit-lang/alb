requires miniprelude

class C t
   where foo :: t -> t

class D t
   where bar :: t -> t

class E t
   where baz :: t -> t

instance D t if C t
   where bar = foo
else D t fails

instance E t if C t
   where baz = foo

f :: D t => t -> t
f = baz

instance C Bool
   where foo = not

main = f False