requires miniprelude
requires test
--tests basic allocation works
--tests rough perforrmance of allocation of
--lists (head allocation

--drives functions
main:: M Unsigned
main = do v <- return (loop 1000 3)
          return v

--allocates a bunch of integers toa  list and then discards the list
--returning the head of the list (which is 3)
allocateLots:: List Unsigned -> Unsigned -> Unsigned
allocateLots acc acc2 = case (acc2) of 1000 -> head acc
                                       x -> allocateLots (Cons 3 acc) (x+1)

--naive loop that calls the allocater function a whole bunch of times
--the let i and j is to study life time of the lists (seems to be working)
loop:: Unsigned -> Unsigned -> Unsigned
loop acc retval = case acc of 0 -> retval 
                              x -> let i = allocateLots Nil 0 in
                                   let j = allocateLots Nil 0 in
                                   loop (acc-1) (i+j)
