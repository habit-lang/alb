requires miniprelude
requires test

main:: M Unsigned
main = do v <- return (eqtester 5)
          return v

eqtester:: Unsigned -> Unsigned
eqtester acc = if acc /= 1000 then 5 else 3


			
