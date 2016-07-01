requires list
requires test

main = do
  x <- runTests (Cons main0 (Cons main1 (Cons main2 (Cons main3 (Cons main4
                 (Cons main5 (Cons main6 (Cons main7 (Cons main8 Nil)))))))))
  return x

main0 :: M Bool
main0 = do x <- return (False == (null (Cons (0::Unsigned) Nil)))
           return x

succ x = x + 1

upto :: Unsigned -> List Unsigned
upto n = iterate n succ 0

lensucc _ y = y + 1

len = foldr lensucc 0

main1 :: M Bool
main1 = do x <- return (100 == (length (upto 100)))
           return x

main2 :: M Bool 
main2 = do x <- return (99 == (last (upto 100)))
           return x

main3 :: M Bool
main3 = do x <- return ((100::Unsigned) == (len (upto 100)))
           return x

main4 :: M Bool
main4 = do x <- return (0 == (length (upto 0)))
           return x

main5 :: M Bool
main5 = do x <- return (1 == (length (upto 1)))
           return x

-- This one dies in backend:

main6 :: M Bool 
main6 = do x <- return
      	        (and (Cons (upto 100 == upto 100)
                     (Cons (upto 100 == reverse (reverse (upto 100)))
                     (Cons (sum (upto 100) == sum (reverse (upto 100)))
                     (Cons (upto 100 == foldr Cons Nil (upto 100))
                     Nil)))))
           return x

bug1 :: M Bool
bug1 = do x <- return (upto 100 == foldr Cons Nil (upto 100))
          return x

-- This one succeeds:

main7 :: M Bool 
main7 = do x <- return
      	        (and (Cons (upto 100 == upto 100)
                     (Cons (upto 100 == reverse (reverse (upto 100)))
                     (Cons (sum (upto 100) == sum (reverse (upto 100)))
                     Nil))))
           return x

singleton x = Cons x Nil
el x = elem x (upto 100)

main8 :: M Bool 
main8 = do x <- return
      	        (and 
                     (Cons (100 == length (upto 100))
                     (Cons (99 == last (upto 100))
                     (Cons (upto 100 == upto 100)
                     (Cons (upto 100 /= (reverse (upto 100)))
                     (Cons (upto 100 == reverse (reverse (upto 100)))
                     (Cons (sum (upto 100) == sum (reverse (upto 100)))
                     (Cons (upto 100 == concat (map singleton (upto 100)))
                     (Cons (False == elem 100 (upto 100))
                     (Cons (True == and (map el (upto 100)))
                     Nil))))))))))
           return x
