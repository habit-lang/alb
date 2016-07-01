primitive type (->) :: * -> * -> *
infixr type 5 ->

data Bool = False | True

not False = True
not True  = False

class Monad m
  where return :: a -> m a
        (>>=)  :: m a -> (a -> m b) -> m b

data List x = Cons x (List x) | Nil

Nil ++ y = y
(Cons x xs) ++ y = Cons x (xs ++ y)

class C t where op :: t -> Bool
instance C (List t) where op x = True

x >> y = x >>= (\x -> y)

p y = (let f x = op (y >> return x) in f :: c -> Bool, y ++ Nil)

q y = (y ++ Nil, let f x = op (y >> return x) in f :: c -> Bool)