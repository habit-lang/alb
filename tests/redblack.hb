--  Hook's first Habit program, based on Okasaki Red Black Tree implementation

requires prelude
requires list
requires test

data Color = R | B
data RedBlackSet a = E | T Color (RedBlackSet a) a (RedBlackSet a)

balance :: Color -> RedBlackSet a -> a -> RedBlackSet a -> RedBlackSet a
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance color a x b = T color a x b

insert :: (Ord a) => a -> RedBlackSet a -> RedBlackSet a
insert x s = case (ins s) of
                T _ a y b -> T B a y b
             where
	        ins E = T R E x E
		ins s@(T color a y b)
		      | x < y = balance color (ins a) y b
		      | x > y = balance color a y (ins b)
		      | True  = s

member :: Ord a => a -> RedBlackSet a -> Bool
member x E = False
member x (T _ a y b)
  | x == y = True
  | x < y = member x a
  | x > y = member x b

main = do
  x <- runTests (Cons main0 (Cons main1 (Cons main2 (Cons main3 (Cons bug1 (Cons main4 (Cons main5 (Cons main6 Nil))))))))
  return x

main0 :: M Bool
main0 = do x <- return (not (member (2::Unsigned) E))
           return x

main1 :: M Bool
main1 = do x <- return (member (2::Unsigned) (insert (2::Unsigned) E))
           return x

main2 :: M Bool
main2 = do x <- return (member (2::Unsigned) (insert (3::Unsigned) (insert (2::Unsigned) E)))
           return x

ss :: Unsigned -> Unsigned
ss x = x + 2

main3 :: M Bool
main3 = do x <- return
                (and (Cons (True == member 8 (foldr insert E (iterate (100::Unsigned) ss (0::Unsigned))))
                     (Cons (False == member 7 (foldr insert E (iterate (100::Unsigned) ss (0::Unsigned))))
                     Nil)))
           return x

bug1 :: M Bool
bug1 = do x <- return (member 8 (foldr insert E (iterate (100::Unsigned) ss (0::Unsigned))))
          return x

main4 :: M Bool
main4 = do x <- return (100 == length (iterate (100::Unsigned) ss (0::Unsigned)))
           return x

listToSet :: Ord a => List a -> RedBlackSet a
listToSet = foldr insert E

m5 :: () -> Bool
m5 _ = let evens = iterate (100::Unsigned) ss (0::Unsigned)
           evenSet = listToSet evens
       in member 8 evenSet

main5 :: M Bool
main5 = do x <- return (m5 ())
           return x

m6 :: () -> Bool
m6 _ = let evens = iterate (100::Unsigned) ss (0::Unsigned)
           evenSet = listToSet evens
       in member 8 evenSet

main6 :: M Bool
main6 = do x <- return (m6 ())
           return x
