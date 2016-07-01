requires qprelude


data Expr t = IntConst Unsigned                   if t == Unsigned
            | IsZero (Expr Unsigned)              if t == Bool
            | Sum (Expr Unsigned) (Expr Unsigned) if t == Unsigned
            | BoolConst Bool                      if t == Bool  
            | And (Expr Bool) (Expr Bool)         if t == Bool
            | If (Expr Bool) (Expr t) (Expr t) 
            | Pair (Expr u) (Expr u')             if t == (u,u')

-- These next two lines require existentials
--            | Fst (Expr (u, u'))                  if t == u
--            | Snd (Expr (u, u'))                  if t == u'


c0 = IntConst 0
c1 = IntConst 1

e0 = If (IsZero c0) c0 c1
e1 = If (IsZero c1) c0 c1
e2 = If (And (IsZero c0) (IsZero c1)) c0 (Sum c0 c1)
e3 = Pair c0 (IsZero c0)
e4 x = Sum c0 x
e5 x = Pair c0 x

-- b0 = If c0 c0 c1
-- b1 = Sum (And (IsZero c0) (IsZero c1)) c1
-- b2 = And (Sum c0 c1) (BoolConst True)

eval :: Expr t -> t
eval (IntConst u)  = u
eval (IsZero e)    = eval e == 0
eval (Sum e e')    = eval e + eval e'
eval (BoolConst b) = b
eval (If e e' e'') = if eval e then eval e' else eval e''
eval (Pair e e')   = (eval e, eval e')

-- As above
-- eval (Fst e)       = fst (eval e)
-- eval (Snd e)       = snd (eval e)

x0 = eval e0
x1 = eval e1
x2 = eval e2
x3 = eval e3

test = (e0, e1, e2, e3, e4 e0, e5 e1,
        x0, x1, x2, x3)

