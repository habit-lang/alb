requires prelude

data List a = (forall b) L ((a -> b -> b) -> b -> b)

fold :: List a -> (a -> b -> b) -> b -> b
fold (L f) = f

map :: (a -> b) -> List a -> List b
map = undefined 

nil :: List a
nil = L (\_ n -> n)

cons :: a -> List a -> List a
cons x xs = L (\c n -> c x (fold xs c n))

hd :: List a -> a
hd l = fold l (\x _ -> x) (undefined)

tl :: List a -> List a
tl l = fst (fold l c n)
  where c x (_, t) = (t, cons x t)
        n          = undefined

concat :: List a -> List a -> List a
concat = undefined  

null :: List a -> Bool
null = undefined
