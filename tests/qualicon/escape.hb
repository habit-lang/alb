requires qprelude

class F (a :: *) (b :: *) | a -> b

data T a = MkT b if F a b

-- Right (Datatype
--         (At :1:6-10 (TyApp (At :1:6-8 (TyCon (Ident "T" 0 Nothing))) (At :1:8-10 (TyVar (Ident "a" 0 Nothing)))))
--         [ Ctor {ctorName = At :1:12-16 (Ident "MkT" 0 Nothing)
--         , ctorParams = []
--         , ctorQualifiers = [At :1:21-26
--                          (Pred (At :1:21-26
--                                    (TyApp (At :1:21-23
--                                           (TyApp (At :1:21-23
--                                                  (TyCon (Ident "F" 0 Nothing)))
--                                                  (At :1:23-25
--                                                  (TyVar (Ident "a" 0 Nothing)))))
--                                                  (At :1:25-26
--                                                  (TyVar (Ident "b" 0 Nothing)))))
--                          Nothing Holds)]
--         , ctorFields = [At :1:16-18 (TyVar (Ident "b" 0 Nothing))]}]
--         []
--         Nothing)


f :: T a -> T a
f (MkT b) = MkT b

g :: (F a b, F a' b) => T a -> T a'
g (MkT b) = MkT b

-- These should not typecheck:
--
-- h :: F a' b => T a -> T a'
-- h (MkT b) = MkT b
--
-- j :: T a -> T a'
-- j (MkT b) = MkT b

-- Neither should these
--
-- data U (a :: *) = C Bool
--                 | D b
--
-- bitdata B = B [ x :: t ]

data Equ a b = Refl if a == b

h z x y =
    j z x y
    (case z of
       Refl -> x < y)

j :: Equ a b -> a -> b -> c -> c
j x y z w = w