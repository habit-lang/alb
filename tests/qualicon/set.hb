requires qprelude
requires ondeckprelude

data Set t = Empty                    if Ord t 
           | Branch t (Set t) (Set t) if Ord t 

m0, m1 :: Set Unsigned
m0 = Empty
m1 = Branch 5 (Branch 1 Empty Empty) (Branch 8 (Branch 6 Empty Empty) (Branch 10 Empty Empty))

-- data UnOrdered = T | U
-- 
-- m2 :: Set UnOrdered
-- m2 = Branch T (Branch U Empty Empty) Empty

insert :: t -> Set t -> Set t
insert t Empty                           = Branch t Empty Empty
insert t (Branch t' left right) | t < t' = Branch t' (insert t left) right
                                | True   = Branch t' left (insert t right)

elem :: t -> Set t -> Bool 
elem t Empty                            = False
elem t (Branch t' left right) | t == t' = True
                              | t < t'  = elem t left
                              | True    = elem t right

x = elem 4 (insert 6 m1)