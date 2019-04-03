requires prelude

struct S [ x, y, z :: Stored Unsigned ]
 deriving (NullInit, NoInit)

external area test = 0x00a <- i :: Ref S
  where  i = nullInit

main = id True
