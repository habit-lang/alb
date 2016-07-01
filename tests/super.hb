data Bool = False | True

class Eq t
   where eq :: t -> t -> Bool

class Ord t | Eq t 
   where lte :: t -> t -> Bool

f :: Ord t => t -> t -> Bool
f x y = eq x y

instance Eq Bool
    where eq True True   = True
          eq False False = True
          eq _ _         = False

instance Ord Bool
    where lte False _   = True
          lte True True = True
          lte _ _       = False

data List t = Nil | Cons t (List t)

instance Eq (List t) if Eq t
    where eq Nil Nil                 = True
          eq (Cons x xs) (Cons y ys) = if eq x y then eq xs ys else False
          eq _ _                     = False 

instance Ord (List t) if Ord t
    where lte Nil Nil                 = True
          lte (Cons x xs) (Cons y ys) = if lte x y then lte xs ys else False
          lte _ _                     = False

          