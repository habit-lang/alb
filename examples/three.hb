requires prelude
requires mem
requires test


main = do
  x <- runTests (map (equalM 3) (Cons main3 (Cons mayne (Cons mine (Cons mane (Cons maine (Cons meh (Cons ma (Cons mania (Cons manna Nil))))))))))
  return x


main3  :: M Unsigned
main3   = do v <- return 3
             return v

mayne  :: M Unsigned
mayne   = do v <- return (let y = 3 in y)
             return v

mine   :: M Unsigned
mine    = do v <- return (1 + 2)
             return v

mane   :: M Unsigned
mane    = do v <- mlength (Cons 1 (Cons 2 (Cons 3 Nil)))
             return v

mlength :: List Unsigned -> M Unsigned
mlength Nil         = return 0
mlength (Cons x xs) = do -- print
	                 s <- mlength xs
                         return (s + 1)

maine  :: M Unsigned
maine   = do v <- return ((plus one two) (\x -> x + 1) 0)
             return v

zero f x   = x
succ n f x = n f (f x)
plus n m   = n succ m
one       = succ zero
two       = succ one

meh :: M Unsigned
meh = do v <- return (bthree 1 1)
         return v

bthree :: Unsigned -> Unsigned -> Unsigned
bthree x y = if x == y then
                if not (y == x) then
                   2
                else
		   3
             else 1


area ne <- (initStored 3) :: Ref(Stored Unsigned)
ma :: M Unsigned

ma = do v <- readRef ne
        case v of
          100000000 -> return 3
          10 -> do writeRef ne (v + 2)
                   ma
          _ -> do writeRef ne (v + 1)
                  ma


area nia <- myinit :: Ref (Array 3 (Stored Unsigned))

myinit :: Init (Array 3 (Stored Unsigned))
myinit = initArray (\x -> initStored (unsigned x))

mania :: M Unsigned
mania = do v <- readRef (nia @ 2)
           writeRef (nia @ 2) (v + 1)
           x <- fooble (nia @ 1)
           mapArray fooble nia
	   w <- readRef (nia @ 2)
           return w

fooble :: Ref (Stored Unsigned) -> M ()
fooble a = do v <- readRef a
              writeRef a (v + 3)


mapArray f a = loop f a 0
  where
    loop f' a' n = case incIx n of
                     Just n' -> f' (a' @ n')
                     Nothing -> return ()

area ne' <- (initStored 3) :: Ref(Stored Unsigned)

farble :: Unsigned -> M ()
farble n = do v <- readRef ne'
              writeRef ne' (v + n)

sequence_ Nil = return ()
sequence_ (Cons l ls) = do x <- l
                           sequence_ ls


manna :: M Unsigned
manna = do v <- readRef ne'
           if v /= 303
           then do x <- sequence_ (map farble (Cons 1 (Cons 2 (Cons 3 Nil))))
                   manna
           else return 3
