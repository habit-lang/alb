requires prelude

struct S [ x, y, z :: Stored Unsigned ]
 deriving (NullInit, NoInit)

external area test = 0x00a <- i :: Ref S
  where  i = nullInit

external area test' = 0x001a :: Ref S

-- area test' <- nullInit :: ARef 4 S

main = id True
