requires prelude

data Either a b = L a | R b

data List a = (forall b) L ((a -> b -> b) -> b -> b)

fold :: List a -> (a -> b -> b) -> b -> b
fold (L f) = f

map :: (a -> b) -> List a -> List b
map = undefined 

nil :: List a
nil = L (\_ n -> n)

cons :: a -> List a -> List a
cons x xs = L (\c n -> c x (fold xs c n))

hd :: List a -> Either a b
hd l = fold l (\x _ -> x) (L "error on head")

tl :: List a -> List a
tl l = fst (fold l c n)
  where c x (_, t) = (t, cons x t)
        n          = error "tl on []"

concat :: List a -> List a -> List a
concat = undefined  

null :: List a -> Boolean
null = undefined

