requires prelude
requires list

id x = x
compose f g x = f (g x)

data (f :+: g) (e :: *) = Inl (f e) | Inr (g e)
(f <?> g) (Inl x) = f x
(f <?> g) (Inr x) = g x
data Fix e = In (e (Fix e))

infix type 5 :+:

class Functor f
    where fmap :: (a -> b) -> f a -> f b

instance Functor (f :+: g) if Functor f, Functor g
    where fmap f (Inl x) = Inl (fmap f x)
          fmap f (Inr x) = Inr (fmap f x)

--------------------------------------------------------------------------------

class In f g
instance In f f
else In f (g :+: h) if In f g
else In f (g :+: h) if In f h
else In f g fails

class f :<: g
   where inj :: f e -> g e

instance f :<: f
   where inj = id
else f :<: (g :+: h) if f :<: g, In f h fails
   where inj = compose Inl inj
else f :<: (g :+: h) if f :<: h, In f g fails
   where inj = compose Inr inj
--else (f :+: g) :<: h if f :<: h, g :<: h
--   where inj = inj <?> inj
else f :<: g fails

--------------------------------------------------------------------------------

class f :-: g = h | f h -> g
    where (?) :: (g e -> r) -> (h e -> r) -> f e -> r

instance (f :+: g) :-: f = g
   where m ? n = m <?> n
else (f :+: g) :-: g = f
   where m ? n = n <?> m
else (f :+: g) :-: h = (f :-: h) :+: g if In h g fails
   where m ? n = (m ? compose n Inl) <?> (compose n Inr)
else (f :+: g) :-: h = f :+: (g :-: h) if In h g fails
   where m ? n = (compose n Inl) <?> (m ? compose n Inr)

--------------------------------------------------------------------------------

cases cs (In e) = cs e (cases cs)
casesUp cs (In e) = cs (fmap (casesUp cs) e)

-- Not sure if this one is useful---haven't sorted out the details of its usage yet.
casesDown cs (In e) = In (fmap (casesDown cs) (cs e))

--------------------------------------------------------------------------------
-- Replacing cases is easy.

(<<?) :: (f :-: g = h, h :<: f) => (g e -> r) -> (f e -> r) -> f e -> r
m <<? n = m ? (n `compose` inj)


--------------------------------------------------------------------------------
-- Example 1: tuples

data CoreExpr e = ECon Unsigned | EApp e e
econ s = In (inj (ECon s))
eapp e e' = In (inj (EApp e e'))

instance Functor CoreExpr
    where fmap f (ECon s) = ECon s
          fmap f (EApp e e') = EApp (f e) (f e')

data TupleExpr e = ETuple (List e) | ETupleCon Unsigned
etuple es = In (inj (ETuple es))
etuplecon n = In (inj (ETupleCon n))

instance Functor TupleExpr
    where fmap f (ETuple es) = ETuple (map f es)
          fmap f (ETupleCon n) = ETupleCon n


rewriteTuples (In e) = (f ? compose In (fmap rewriteTuples)) e
    where f (ETuple es)   = foldl eapp (econ (length es)) (map rewriteTuples es)
          f (ETupleCon n) = econ n

rewriteTuples' = casesUp (tupleCase ? In)
    where tupleCase (ETuple es) = foldl eapp (econ (length es)) es
          tupleCase (ETupleCon n) = econ n

f :: Fix (CoreExpr :+: TupleExpr) -> Fix CoreExpr
f = rewriteTuples

f' :: Fix (TupleExpr :+: CoreExpr) -> Fix CoreExpr
f' = rewriteTuples

--------------------------------------------------------------------------------
-- Example 2: expressions

data Const (e :: *) = Const Unsigned
data Sum e = Sum e e
data Product e = Product e e

type ExprOne = Fix (Const :+: Sum)
type ExprTwo = Fix ((Const :+: Sum) :+: Product)
type ExprThree = Fix (Const :+: (Sum :+: Product))

const_ i = In (inj (Const i))
sum_ x y = In (inj (Sum x y))
product_ x y = In (inj (Product x y))

one :: ExprOne
one = sum_ (const_ 1) (const_ 2)

two :: ExprTwo
two = sum_ (const_ 1) (product_ (const_ 2) (const_ 3))

three :: ExprThree
three = sum_ (const_ 1) (product_ (const_ 2) (const_ 3))

evalConst (Const u) r = u
evalSum (Sum x y) r = r x + r y
evalProduct (Product x y) r = r x * r y

evalOne = cases (evalConst ? evalSum)
x       = evalOne one

evalTwo = cases (evalConst ? (evalSum ? evalProduct))
y       = evalTwo two
z       = evalTwo three

main = (x, y, z)
