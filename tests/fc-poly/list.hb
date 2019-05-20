-- requires prelude
requires base

data List a = (forall e) L ((a -> e -> e) -> e -> e)

fold :: List a -> (a -> b -> b) -> b -> b
fold (L f) = f

nil :: List a
nil = L (\_ n -> n)

cons :: a -> List a -> List a
cons x xs = L (\c n -> c x (fold xs c n))

hd :: List a -> a
hd l = fold l (\x _ -> x) (undefined)

-- tl :: List a -> List a
-- tl l = fst (fold l c n)
--   where c x (_, t) = (t, cons x t)
--         n          = undefined

-- map :: (a -> b) -> List a -> List b
-- map = \f -> \l -> (fold l) (cons `compose` f) nil

-- concat :: List a -> List a -> List a
-- concat l r = (fold l) cons r  

-- null :: List a -> Bool
-- null = undefined
