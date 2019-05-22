requires prelude
requires list

data Stack a = (forall xs) MkStack xs        -- self
                             (a -> xs -> xs) -- push
                             (xs -> xs)      -- pop
                             (xs -> a)       -- top
                             (xs -> Bool)    -- empty


makeListStack :: List a -> Stack a
makeListStack l = MkStack l cons tl hd null

push :: a -> Stack a -> Stack a
push x (MkStack self push' pop top empty) = MkStack (push' x self) push' pop top empty

top :: Stack a -> a
top (MkStack self push pop top' empty)
    = top' self

l1 = makeListStack (cons 1 (cons 2 (cons (3) nil)))
l2 = makeListStack (cons 4 (cons (5) nil))

testExpr :: List Unsigned
testExpr  = map (top `compose` push 1) (cons l1 (cons l2 nil))