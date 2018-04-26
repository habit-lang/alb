requires qprelude


-- shared non-empty list
data NEList a = Last a | Cons' !! a (NEList a)

-- head' :: NEList a -> a
head'   = \xs -> case xs of
                   Last x     ->  x
                   Cons' x ys ->  x

-- TODO what about this?
concat' (Last a) as' = Cons' a as'
concat' (Cons' a as) as' = Cons' a (concat' as as')

-- concat' ::  (SeFun f) => NEList a ->{f} NEList a ->{g} NEList a
-- concat' xs xs' = case xs of
--                    Last x -> Cons' x xs'
--                    Cons' x ys -> Cons' x (concat' ys xs')

-- separating list
data List a = Nil | Cons a (List a)

tail :: (Un a) => List a -> List a
tail = \xs -> case xs of
                Nil ->  Nil
                Cons a as ->  as

-- concat :: (SeFun f, SeFun g) => List a ->{f} List a ->{g} List a
-- concat Nil as' = as'
-- concat (Cons a as) as' = Cons a (concat as as')