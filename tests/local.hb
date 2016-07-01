requires miniprelude

data Pair t = Pair t t

h x z = 
  let f y = Pair x y
  in f z  

g :: a -> (a -> Pair a)
g x z = 
  let f y = Pair x y
  in f z  
