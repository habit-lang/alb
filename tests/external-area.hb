requires test
requires prelude

struct S [ x, y, z :: Stored Unsigned ]
 deriving (NullInit, NoInit)

-- Works fine
external area test = 0x00a <- i :: Ref S
  where  i = nullInit

area test' <- i :: Ref S
  where  i = nullInit

-- This fails due to context too weak 
-- external area test'' = 0x001a :: Ref S

main = do
  x <- runTests ((Cons (return (True == True)) Nil))
  return x
