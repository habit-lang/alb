module Fidget.Env where

{- Environments -}
{- A completely simplistic implementation just for now -}

{- Env's are the running environment of the fidget interpreter?
 - this is basically a naive key value pair, keys are type a, values are type
 - b. Empty env is the empty list of key value pairs, lookup either finds the value associated with a key, or errors
 - extend adds a new key to the dictionary-}
data Env a b = Env [(a,b)]

empty_env :: Eq a => Env a b
empty_env = Env []

lookup_env :: (Eq a,Show a) => Env a b -> a -> b -- may error
lookup_env (Env []) a = error ("lookup_env failed:" ++ (show a))
lookup_env (Env ((a,b):e)) a' = if a == a' then b else lookup_env (Env e) a'

extend_env :: Eq a => Env a b -> a -> b -> Env a b 
extend_env (Env e) a b = Env ((a,b):e)
