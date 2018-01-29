requires prelude

data List a = Nil | Cons a (List a)

instance Eq (List a) if Eq a
  where Nil         == Nil         = True
        (Cons x xs) == (Cons y ys) = x == y && xs == ys
        _           == _           = False

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

reverse xs = rev Nil xs
  where rev rs Nil         = rs
        rev rs (Cons x xs) = rev (Cons x rs) xs

append Nil ys         = ys
append (Cons x xs) ys = Cons x (append xs ys)

head (Cons x xs) = x

last xs = head (reverse xs)

tail (Cons x xs) = xs

-- init xs = reverse (tail (reverse xs))

null Nil        = True
null (Cons _ _) = False

length :: List a -> Unsigned
length Nil = 0
length (Cons _ xs) = 1 + length xs

foldr :: (a -> b -> b) -> b -> List a -> b
foldr c n Nil = n
foldr c n (Cons x xs) = c x (foldr c n xs)

foldl :: (a -> b -> a) -> a -> List b -> a
foldl c n xs = afold c n xs
  where afold c r Nil = r
        afold c r (Cons x xs) = afold c (c r x) xs

concat :: List (List a) -> List a
concat = foldr append Nil

sum = foldr (+) 0

and :: List Bool -> Bool
and Nil = True
and (Cons x xs) = x && and xs

or :: List Bool -> Bool
or Nil = False
or (Cons x xs) = x || or xs

any :: (a -> Bool) -> List a -> Bool
any _ Nil = False
any p (Cons x xs) = p x || any p xs

all :: (a -> Bool) -> List a -> Bool
all _ Nil = True
all p (Cons x xs) = p x && all p xs

take n _ | n <= 0  = Nil
take _ Nil         = Nil
take n (Cons x xs) = Cons x (take (n - 1) xs)

drop n xs | n <= 0 = xs
drop _ Nil         = Nil
drop n (Cons _ xs) = drop (n - 1) xs

splitAt n xs = (take n xs, drop n xs)

replicate n _ | n <= 0 = Nil
replicate n x          = Cons x (replicate (n-1) x)

iterate n f x | n <= 0 = Nil
iterate n f x          = Cons x (iterate (n-1) f (f x))

filter :: (a -> Bool) -> List a -> List a
filter _ Nil = Nil
filter p (Cons x xs) | p x  = Cons x (filter p xs)
                     | True = filter p xs

elem :: Eq a => a -> List a -> Bool
elem _ Nil = False
elem y (Cons x xs) | x == y = True
                   | True    = elem y xs

lookup :: Eq a => a -> List (a,b) -> Maybe b
lookup _ Nil = Nothing
lookup k (Cons (x,y) xs) | k == x = Just y
                         | True   = lookup k xs

(!!) :: List a -> Unsigned -> a
(!!) (Cons x _) 0 = x
(!!) (Cons _ xs) n = xs !! (n-1)
-- (!!) _ _ = error 1 -- We might want to agree on a (useful!) error and its type
