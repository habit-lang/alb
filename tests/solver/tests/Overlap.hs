module Tests.Overlap where

import Parser
import Solver

--------------------------------------------------------------------------------
-- Overlap tests

p = q' predicate
qp = q' qpred
ax = q' axiom

a = [qp "Eq a => Eq (L a)", qp "(Eq a, Eq b) => Eq (P a b)"]
f = [p "Eq Int", p "Eq Bool"]

a' = [qp "Eq a => Eq (L a)", qp "Eq (F a b) fails"]
f' = [p "Eq (F a b)"]

t0 = overlapping [] (qp "Eq Int") (qp "Eq Bool")
t1 = overlapping [] (qp "Eq Int") (qp "Eq t")
t2 = overlapping [] (qp "Eq t") (qp "Eq Int")
t3 = overlapping [] (qp "Eq Int") (qp "Eq Int")
t4 = overlapping [] (qp "Eq t") (qp "Eq t")

b0 = and [not t0, t1, t2, t3, t4]

t5 = overlapping [] (qp "Eq a => Eq (L a)") (qp "Eq (L a)")
t6 = overlapping [] (qp "Eq a => Eq (L a)") (qp "Eq a fails => Eq (L a)")
t7 = overlapping [] (qp "Eq a => Eq (L a)") (qp "Qe q => Eq (L a)")

b1 = and [t5, not t6, t7]

t8 = overlapping [ax "Eq T fails"] (qp "Eq a => Eq (L a)") (qp "Eq (L T)")
t9 = overlapping [ax "Eq T"] (qp "Eq t fails => Eq (L t)") (qp "Eq (L T)")
t10 = overlapping [ax "C t => D t fails"] (qp "C t => F t") (qp "D t => F t")
t11 = overlapping [ax "C t => D t fails"] (qp "C t => F t") (qp "D t fails => F t")

b2 = and [not t8, not t9, not t10, t11]



main = print (and [b0, b1, b2])