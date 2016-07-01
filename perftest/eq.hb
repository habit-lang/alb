requires miniprelude
requires test

main = do x <- runTests (map (equalM 3) (Cons (eqtester 1000) Nil))
	  return x

eqtester:: Unsigned -> M Unsigned
eqtester acc = if acc == 1000 then return 3 else return 5


			
