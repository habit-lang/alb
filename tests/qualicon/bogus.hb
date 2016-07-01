requires qprelude, ondeckprelude

data T a = C Unsigned if a == Bool
         | D a 

-- f :: T a -> Bool -> Bool
f (C n) r = n > 0
f (D _) r = pmNot r

g :: T a -> a -> a
g (C n) r = n > 0
g (D _) r = r 