data Pair x y = Pair x y 

Pair x y = Pair True False

Pair f g | True = Pair (\x -> x) (\x -> True)

-- w :: Unsigned
-- Pair z w = Pair False 0

-- Pair ff gg = Pair (\x y -> x == y) (\x y -> x < y)

data DictEq t = DictEq (t -> t -> Bool) (t -> t -> Bool)
DictEq fff ggg = DictEq ((==) :: Bool -> Bool -> Bool) (/=)





main = fff True False && ggg False False

