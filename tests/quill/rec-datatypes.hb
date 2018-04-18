requires qprelude

data NEList a = Last a | Cons !! a (NEList a)

-- head :: NEList a -> a
head (Last a) = a
head (Cons a as) = a
