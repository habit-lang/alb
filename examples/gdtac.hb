requires prelude
requires io

compose f g x = f (g x)

data (f :+: g) (e :: *) = Inl (f e) | Inr (g e)
(f <?> g) (Inl x) = f x
(f <?> g) (Inr x) = g x

class In f g
instance In f f
else In f (g :+: h) if In f g
else In f (g :+: h) if In f h
else In f g fails

class f :<: g
   where inj :: f e -> g e

instance f :<: f
   where inj = id
else (f :+: g) :<: h if f :<: h, g :<: h
   where inj = inj <?> inj
else f :<: (g :+: h) if f :<: g, In f h fails
   where inj = compose Inl inj
else f :<: (g :+: h) if f :<: h, In f g fails
   where inj = compose Inr inj
else f :<: g fails

data Const (e :: *) = Const Unsigned
data Sum e = Sum e e
data Product e = Product e e

-- Expressions

data Expr e = In (e (Expr e))

type ExprOne = Expr (Const :+: Sum)
type ExprTwo = Expr ((Const :+: Sum) :+: Product)
type ExprThree = Expr (Const :+: (Sum :+: Product))

-- Smart constructors

const_ i = In (inj (Const i))
sum_ x y = In (inj (Sum x y))
product_ x y = In (inj (Product x y))

one :: ExprOne
one = sum_ (const_ 1) (const_ 2)

two :: ExprTwo
two = sum_ (const_ 1) (product_ (const_ 2) (const_ 3))

three :: ExprThree
three = sum_ (const_ 1) (product_ (const_ 2) (const_ 3))

-- Evaluation

class f :-: g = h | f h -> g
    where (?) :: (g e -> r) -> (h e -> r) -> f e -> r

instance (f :+: g) :-: f = g
   where m ? n = m <?> n
else (f :+: g) :-: g = f
   where m ? n = n <?> m
else (f :+: g) :-: h = (f :-: h) :+: g if In h g fails
   where m ? n = (m ? compose n Inl) <?> (compose n Inr)
else (f :+: g) :-: h = f :+: (g :-: h) if In h f fails
   where m ? n = (compose n Inl) <?> (m ? compose n Inr)

evalConst (Const u) r = u
evalSum (Sum x y) r = r x + r y
evalProduct (Product x y) r = r x * r y

cases cs = f where f (In e) = cs e f

evalOne = cases (evalSum ? evalConst)
x       = evalOne one

evalTwo = cases (evalConst ? (evalSum ? evalProduct))
y       = evalTwo two
z       = evalTwo three

-- Desugaring

class Functor f
    where fmap :: (a -> b) -> f a -> f b

instance Functor (f :+: g) if Functor f, Functor g
    where fmap f (Inl m) = Inl (fmap f m)
          fmap f (Inr m) = Inr (fmap f m)

instance Functor Const
    where fmap f (Const x) = Const x

instance Functor Sum
    where fmap f (Sum m n) = Sum (f m) (f n)

instance Functor Product
    where fmap f (Product m n) = Product (f m) (f n)

data Double e = Double e
double_ e = In (inj (Double e))
desugar = cases ((\(Double e) r -> sum_ (r e) (r e)) ?
                 (const `compose` In `compose` fmap desugar))

type ExprFour = Expr (Const :+: (Sum :+: (Product :+: Double)))
four :: ExprFour
four = sum_ (const_ 1) (double_ (const_ 2))
w    = evalTwo (desugar four)

main = do putint x
          putint y
          putint z
          putint w
