requires miniprelude
requires test
--This file has several different versions of the ackermann
--function, as it's a somewhat complex function that can
--reveal issues in code (static analyzers can't deal with it
--very well in my experience)
--
--It's shown some problems with allocation lifetime

--Main function just calls one of the functions
main::M Unsigned
main = do x <- return (ackermanntest 4 4)
          return x

--An explecit version, no sugar
ackermann :: Unsigned -> Unsigned -> Unsigned
ackermann m n = case (m,n) of (0,x) -> x+1
                              (x,0) -> ackermann (x-1) 1
                              (x,y) -> ackermann (x-1) (ackermann x (y-1))

--A somewhat sugared version
ackermanntest :: Unsigned -> Unsigned -> Unsigned
ackermanntest m n | m == 0 = n+1
                  | n == 0 = ackermanntest (m-1) 1
                  | m > 0 && n > 0 = ackermanntest (m-1) (ackermann m (n-1))


			
