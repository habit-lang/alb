requires prelude
requires io

fib :: Signed -> Signed
fib n
 | n < 2 = n
 | otherwise = fib (n - 1) + fib (n - 2)

main :: M Unsigned
main = do x <- return ()
          putint (unsigned (fib 15))
          return (unsigned (fib 15))
