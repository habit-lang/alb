requires miniprelude
requires test
requires newbool

main:: M Unsigned
main = do v <- return (eqtester 5)
          return v

eqtester:: Unsigned -> Unsigned
eqtester acc = if myNot(acc == 1000) then 5 else 3


			
