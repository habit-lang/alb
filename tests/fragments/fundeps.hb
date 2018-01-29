requires prelude
requires list

data Int

class F (a :: *) = (b :: *)
   where foo :: a -> b

instance F Int = Bool
   where foo _ = True

instance F Bool = _
   where foo = primFoo

primitive primFoo :: Bool -> F Bool

instance F (List t) = List u if F t = u
   where foo (Cons x xs) = Cons (foo x) Nil

notb True  = False
notb False = True

g :: F Int b => b -> b
g x = notb x

h :: F Int b => b -> b
h = notb

class Equal t u | t -> u, u -> t
    where ident :: t -> u

instance Equal t t
    where ident x = x

r :: t -> t
r x = ident x

s :: Equal t u => t -> u
s x = x