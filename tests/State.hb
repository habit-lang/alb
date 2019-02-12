-- requires prelude
requires test

data State s a = S (s -> (a, s))

instance Monad (State s) where
  return a = S (\ s -> (a, s))
  (S m) >>= f = S (\s -> case m s of
                           (a, s') -> case f a of
                                        S f' -> f' s')

get :: Unit -> State s s
get _ = S (\s -> (s, s))

put :: s -> State s ()
put s = S (\s' -> ((), s))

type MyS s = State Unsigned s

incr :: Unit -> MyS ()
incr _ = do
  s <- get ()
  put (s + 1)

execState :: State s a -> s -> s
execState (S f) s = case f s of
                      (_, s') -> s'

evalState :: State s a -> s -> a
evalState (S f) s = case f s of
                      (a, _) -> a

main :: M Unsigned
main = do
  x <- runTests (Cons (return (1 == evalState (incr () >>= (\ x -> get ())) 0)) Nil)
  return x


-- main = 1 == evalState (incr () >>= (\ x -> get ())) 0