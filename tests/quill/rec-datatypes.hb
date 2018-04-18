requires qprelude


-- shared non-empty list
data NEList a = Last a | Cons' !! a (NEList a)

-- head' :: NEList a -> a
head' (Last a) = a
head' (Cons' a as) = a

-- separating list
data List a = Nil | Cons a (List a)

tail :: (Un a) => List a -> List a
tail Nil = Nil
tail (Cons a as) = as