data Either a b = Left a | Right b

data T t =   (forall u) MkT1 t u 
            | (forall v) MkT2 (v t) 

-- data SillyPair a = MkSP a List b forall b

-- length :: List a -> Int
-- length = undefined

-- f :: Pair Int -> Int
-- f (MkPair a l) = length l
