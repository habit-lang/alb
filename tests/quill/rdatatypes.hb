requires qprelude


-- shared non-empty list
data NEList a = Last a | Cons' !! a (NEList a)

instance Un (NEList a) if Un a
else Un (NEList a) fails

-- head' :: NEList a -> a
head'   = \xs -> case xs of
                   Last x     ->  x
                   Cons' x ys ->  x

-- TODO what about this?
-- concat' (Last a) as' = Cons' a as'
-- concat' (Cons' a as) as' = Cons' a (concat' as as')

concat' ::  (ShFun f, ShFun g, (NEList a) >:= ((NEList a) ->{g} (NEList a))) => NEList a ->{f} NEList a ->{g} NEList a
concat' xs xs' = case xs of
                   Last x -> Cons' x xs'
                   Cons' x ys -> Cons' x (concat' ys xs')

-- separating list
data List a = Nil | Cons a (List a)

instance Un (List a) if Un a
else Un (List a) fails

tail :: (Un a) => List a -> List a
tail = \xs -> case xs of
                Nil ->  Nil
                Cons a as ->  as

concat :: (SeFun f, SeFun g, (List a) >:= ((List a) ->{g} (List a))) => List a ->{f} List a ->{g} List a
concat Nil as' = as'
concat (Cons a as) as' = Cons a (concat as as')
