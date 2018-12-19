requires prelude
requires io

data Ord a => BST a = Leaf | Node a (BST a) (BST a)

empty :: BST a
empty = Leaf

insert :: a -> BST a -> BST a
insert x Leaf = Node x Leaf Leaf
insert x t@(Node y l r)
  | x == y = t
  | x < y  = Node y (insert x l) r
  | x > y  = Node y l (insert x r)

tree1 = insert (1 :: Unsigned) (insert 2 (insert 3 empty))
tree2 = insert (2 :: Signed) (insert 4 (insert (negate 2) empty))
-- Should fail:
-- three3 = insert (id :: Unsigned -> Unsigned) empty

printInOrder Leaf = return ()
printInOrder (Node x l r) = do printInOrder l
                               putint (unsigned x)
                               putStr " "
                               printInOrder r

class Functor f
    where fmap :: (a -> b) -> f a -> f b

-- To avoid tedium, assuming that f is monotonic...
instance Functor BST
    where fmap f Leaf = Leaf
          fmap f (Node y l r) = Node (f y) (fmap f l) (fmap f r)

telem :: a -> BST a -> Bool
telem x Leaf = False
telem x (Node y l r)
  | x == y = True
  | x < y  = telem x l
  | x > y  = telem x r

allIn :: BST a -> BST a -> Bool
allIn Leaf _ = True
allIn (Node x l r) t = telem x t && allIn l t && allIn r t

instance Eq (BST a)
    where t == u = allIn t u && allIn u t

main = do printInOrder tree1
          putLine
          printInOrder tree2
          putLine
          printInOrder (fmap (1 +) tree1)
          putLine
          if fmap (1 +) tree2 == tree2 then putint 0 else putint 1