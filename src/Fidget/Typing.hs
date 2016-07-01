module Fidget.Typing (type_of_expr, type_of_atom) where

import Fidget.AST

third :: (a, b, c) -> c
third (_, _, c) = c

type_of_atom :: Atom -> Ftyp 
type_of_atom (Avar _ t) = t
type_of_atom (Aconst (Ounit)) = Funit
type_of_atom (Aconst (Ointconst _)) = Fint
type_of_atom (Aconst (Oarea _ a)) = Fref a
type_of_atom (Aload _ _ t) = t
type_of_atom (Aat _ _ a) = Fref a
type_of_atom (Asel _ _ a) = Fref a
type_of_atom (Aunop (Orelax _ m) _) = Fix m
type_of_atom (Aunop (Omodix n) _) = Fix n
type_of_atom (Aunop _ _) = Fint
type_of_atom (Abinop _ _ _) = Fint

type_of_expr :: Expr -> Ftyp
type_of_expr (Eatom a) = type_of_atom a
type_of_expr (Elet _ _ _ body) = type_of_expr body
type_of_expr (Eletrec _ body) = type_of_expr body
type_of_expr (Eifthenelse _ e1 e2) = glb_of (type_of_expr e1) (type_of_expr e2)
type_of_expr (Ecase _ bs Nothing) = foldr1 glb_of (map (type_of_expr . third) bs) 
type_of_expr (Ecase _ bs (Just (_,e))) = foldr1 glb_of $ (type_of_expr e):(map (type_of_expr . third) bs) 
type_of_expr (Eixcase _ _ _ e1 e2) = glb_of (type_of_expr e1) (type_of_expr e2)
type_of_expr (Eerror typ) = typ
type_of_expr (Eletlabel _ body) = type_of_expr body
type_of_expr (Egoto _ _ typ) = typ

-- calculate greatest lower bound of two types... ripped directly from Fidget.v
--
-- the consensus is this should be least upper bound, not greatest lower bound
--
glb_of :: Ftyp -> Ftyp -> Ftyp
glb_of t1 t2 = if is_subtype_of t1 t2
               then t2
               else if is_subtype_of t2 t1
                    then t1
                    else case (t1,t2) of
                      (Frecordt tc1 _, Frecordt tc2 _) -> if tc1 == tc2
                                                          then Ftcon tc1
                                                          else Funit
                      _ -> Funit

is_subtype_of :: Ftyp -> Ftyp -> Bool
is_subtype_of t1 t2 = case (t1,t2) of
  (Frecordt tc1 _, Ftcon tc2) -> tc1 == tc2
  _ -> teq t1 t2

teq :: Ftyp -> Ftyp -> Bool
teq t1 t2 = case (t1,t2) of
  (Funit, Funit) -> True
  (Fint, Fint) -> True
  (Ftcon tc1, Ftcon tc2) -> tc1 == tc2
  (Frecordt tc1 n1, Frecordt tc2 n2) -> tc1 == tc2 && n1 == n2
  (Ffun ts1 res1, Ffun ts2 res2) -> (and $ zipWith teq ts1 ts2) && teq res1 res2
  (Fix m, Fix n) -> m == n
  (Fref a, Fref b) -> aeq a b
  _ -> False

aeq :: Area -> Area -> Bool
aeq a b = case (a,b) of
    (Stored c, Stored d) -> teq c d
    (Array c m, Array d n) -> aeq c d && m == n
    (Struct v, Struct w) -> v == w
    _ -> False
