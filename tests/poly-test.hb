data Either a b = Left a | Right b

data T t =   MkT1 t u forall u
            | MkT2 (v t) forall v


-- data SillyPair a = MkSP a List b forall b

-- length :: List a -> Int
-- length = undefined

-- f :: Pair Int -> Int
-- f (MkPair a l) = length l
