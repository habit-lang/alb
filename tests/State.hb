requires miniprelude
requires test

data Prod a b = Pair a b

data State s a = S (s -> Prod a s)

instance Monad (State s) where
  return a = S (\ s -> Pair a s)
  (S m) >>= f = S (\s -> case m s of
                           Pair a s' -> case f a of 
                                           S f' -> f' s')

get :: Unit -> State s s
get _ = S (\s -> Pair s s)

put :: s -> State s ()
put s = S (\s' -> Pair () s)

type MyS s = State Unsigned s

incr :: Unit -> MyS ()
incr _ = do
  s <- get ()
  put (s + 1)

execState :: State s a -> s -> s
execState (S f) s = case f s of
                      Pair _ s' -> s'

evalState :: State s a -> s -> a
evalState (S f) s = case f s of
                      Pair a _ -> a

main :: M Unsigned
main = do
  x <- runTests (Cons (return (1 == evalState (incr () >>= (\ x -> get ())) 0)) Nil)
  return x
