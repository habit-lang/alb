-- Partial data types: ------------------------------------------

class (@) (t :: k' -> k) (u :: k')

--

data Bool = True | False

data Either a b = Left a | Right b

lt :: Either Bool Bool
lt = Left True

data T t =   (forall u) MkT1 t u 
            | (forall v) MkT2 (v t) 

-- t1 :: T Bool
-- t1 = MkT2 True True 

-- data SillyPair a = MkSP a List b forall b

-- length :: List a -> Int
-- length = undefined

-- f :: Pair Int -> Int
-- f (MkPair a l) = length l
main = lt
