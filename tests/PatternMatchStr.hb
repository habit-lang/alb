requires prelude
requires list
requires io

pat :: List Unsigned -> M Unsigned

pat "hello" = putStr "hello"
pat _ = putStr "hello"

main :: M Unsigned
main = do pat "hello"
          pat "asldfjla"
          return (0)



