requires qprelude

-- Standard types and classes

-- data Unit = Unit
-- instance Un Unit

data Bool = False | True
instance Un Bool

otherwise :: Bool
otherwise = True

not :: Bool -> Bool
not True = False
not False = True

-- data Ordering = LT | EQ | GT
-- instance Un Ordering

data Choice a b = L a | R b
data Pair a b = P a b
data Pair' a b = ShP !! a b
data Sh3Tuple a b c = Sh3P !! a b c
data Mix3Tuple a b c = Mx3Tp !! a (Pair b c)

-- ctob :: (->) f => f (Choice a b) -> Bool
-- ctob x = {( L a <- x => ^False | R b <- x => ^False )}
--              g => commit False | g => commit False

ctob :: Choice Bool Bool -> Bool
ctob (L x) = x
ctob (R y) = y

ctob' :: {- (Un a, Un b, SeFun f) =>-} Choice a b ->{f} Pair (Choice a b) Bool
ctob' (L x) = P (L x) True
ctob' (R y) = P (R y) False

-- fstp :: Pair' a b -> a
fstp (ShP x y) = x
sndp (ShP x y) = y

-- swap :: (SeFun f) => Pair a b ->{f} Pair b a
swap (P x y) = P y x

fst :: (Un c) => Pair b c -> b
fst (P x y) = x

snd :: (Un a) => Pair a b -> b
snd (P a b) = b

fstp3 (Sh3P a b c) = a
sndp3 (Sh3P a b c) = b
trdp3 (Sh3P a b c) = c

lprj (Mx3Tp a p) = a

rprj1 :: (Un c) => Mix3Tuple a b c ->{f} b
rprj1 (Mx3Tp a (P c d)) = c

-- TODO This fails
rprj1' :: (Un c) => Mix3Tuple a b c -> b
rprj1' (Mx3Tp a p) = fst p
