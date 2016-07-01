requires miniprelude
requires test
requires newbool

main:: M Unsigned
main = do v <- return (eqtester 5 209563)
          return v

eqtester:: Unsigned-> Unsigned -> Unsigned
eqtester input acc = case acc of 0 -> if myNot(acc == 1000) then 5 else 3
		                 x -> eqtester input (acc-1)


			
