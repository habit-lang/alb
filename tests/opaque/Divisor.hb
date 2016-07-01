requires miniprelude

class C t u | t -> u, opaque u
    where m :: t -> Maybe u
          n :: t -> u -> t

instance C Unsigned Unsigned
    where m 0   = Nothing
          m x   = Just x
          n x y = x * y

f :: Unsigned -> Unsigned
f x = case m x of
        Nothing -> x
        Just y  -> n x y

g :: C Unsigned Unsigned => Unsigned -> Unsigned
g x = n x 0

-- Error!
-- g' :: Unsigned -> Unsigned
-- g' x = n x 0

h :: C Unsigned t => Unsigned -> Maybe t
h x = m (x + 1)

-- Error!
-- h' :: Unsigned -> Maybe Unsigned
-- h' x = m (x + 1)