requires prelude
requires list

class Eq2 t
    where eq, neq :: t -> t -> Bool
          neq x y = not (eq x y)

-- an implicitly typed, recursive, overloaded, function binding:
member x Nil                     = False
member x (Cons y ys) | eq x y    = True
                     | otherwise = member x ys

instance Eq2 Bool
    where eq True True   = True
          eq False False = True
          eq _ _         = False

instance Eq2 (List t) if Eq2 t
    where eq Nil Nil                 = True
          eq (Cons x xs) (Cons y ys) = if eq x y then eq xs ys else False
          eq _ _                     = False

class Integral (t :: *)
class Fractional (t :: *)
class RealFrac t | Fractional t
   where floor :: Integral u => t -> u

data Float
instance Fractional Float
instance RealFrac Float
    where floor = floatFloor

primitive floatFloor :: Integral u => Float -> u

xor x y = neq x y

main = eq (eq (Cons True (Cons False Nil)) Nil)
          (member True (Cons False Nil))

nestedLists = Cons (Cons True Nil) Nil
