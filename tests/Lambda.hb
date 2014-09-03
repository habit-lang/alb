requires prelude
requires test

instance Monad Maybe
   where return = Just
         (Just i) >>= f = f i
         Nothing >>= f = Nothing

data Ty = TyNat | TyFun Ty Ty

instance Eq Ty where
   TyNat == TyNat = True
   TyNat == _ = False
   _ == TyNat = False
   TyFun t1 t2 == TyFun t1' t2' = (t1 == t1') && (t2 == t2')

data Lam = Var Unsigned | Abs Ty Lam | App Lam Lam | Zero | Suc Lam
data List a = Nil | Cons a (List a)

type Env = List Ty

env_lookup :: List a -> Unsigned -> Maybe a
env_lookup Nil i = Nothing
env_lookup (Cons x xs) i | i == 0 = Just x
                         | True = env_lookup xs (i - 1)

typecheck :: Env -> Lam -> Maybe Ty
typecheck e (Var i) = case (env_lookup e i) of
                       Nothing -> Nothing
                       Just t -> Just t
typecheck e Zero = return TyNat
typecheck e (Suc l) = do
                  t <- typecheck e l
                  case t of
                    TyNat -> return TyNat
                    _ -> Nothing
typecheck e (App l l') = do
                  t <- typecheck e l
                  t' <- typecheck e l'
                  case t of
                   TyFun t1 t2 -> if t' == t1 then return t2 else Nothing
                   _ -> Nothing
typecheck e (Abs t1 l) = do
                  t2 <- typecheck (Cons t1 e) l
                  return (TyFun t1 t2)

main :: M Unsigned
main = do
  x <- runTests (Cons (return (Just (TyFun TyNat TyNat) == typecheck Nil (Abs TyNat (Var 0)))) Nil)
  return x
