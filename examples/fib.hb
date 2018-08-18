requires prelude
requires io

fib :: Unsigned -> Unsigned
fib 0 = 1
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

main :: M Unsigned
main = do x <- return ()
          putint (fib 15)
          return (fib 15)
