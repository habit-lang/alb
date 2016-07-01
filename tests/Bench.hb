-- a very simple loop for playing with Fidget optimizations

requires miniprelude

area a <- (initStored 0) :: Ref (Stored Unsigned)

loop :: Unsigned -> Ref (Stored Unsigned) -> M ()
loop 0 _ = return ()
loop n a = do i <- readRef a
              writeRef a (i + 1)
              loop (n - 1) a
              
-- nesting loops in hopes of avoiding blowing the stack              
big_loop :: Unsigned -> Ref (Stored Unsigned) -> M ()
big_loop 0 _ = return ()
big_loop n a = do loop 10000 a
                  big_loop (n-1) a
                  
main :: M Unsigned                  
main = do big_loop 10000 a
          return 3
                   
