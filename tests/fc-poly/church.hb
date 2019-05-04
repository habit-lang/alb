requires prelude

---------- Church Numerals ----------------

data Church = (forall a) Ch ((a -> a) -> (a -> a))

unCh :: Church -> (a -> a) -> (a -> a)
unCh (Ch n) = n

zero, one :: Church
zero = Ch (\_ x -> x)
one  = Ch (\f x -> f x)

succ :: Church -> Church
succ n = Ch (\f -> \x -> (unCh n f (f x)))

pred :: Church -> Church
pred n  = fst (unCh n s z)
  where s (_, y) = (y, succ y)
        z        = z

isZero :: Church -> Bool
isZero n = unCh n (\_ -> False) True

add, mul :: Church -> Church -> Church
add n m = unCh n succ m
mul n m = unCh n (add m) zero
