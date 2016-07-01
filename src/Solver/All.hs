module Solver.All where

import Solver.Main
import Solver.REPL
import Solver.Subst
import Solver.Syntax
import Solver.Tactics
import Solver.Parser
import Solver.PP
import Solver.Validation

import Control.Monad
import Control.Monad.State
import Data.List
import Debug.Trace
import Prelude hiding (even, odd)

--------------------------------------------------------------------------------
-- Testing

ty = q' typ
p = q' predicate
qp = q' qpred
ax = q' axiom
fd = q' funDepRule
rq = q' requirement

s :: StateT Int (Either String) t -> Either String t
s x = evalStateT x (0 :: Int)

--------------------------------------------------------------------------------

dtac = [ax "In f f; In f (Plus g h) if In f g; In f (Plus g h) if In f h; In f g fails"]
dtac2 = [ax "In f f; In f (Plus g h) fails if In f g, In f h; In f (Plus g h) if In f g; In f (Plus g h) if In f h; In f g fails"]
dtac3 = [ ax "In f f; In f (Plus g h) if In f g; In f (Plus g h) if In f h; In f g fails"
        , ax "UniqueIn f f; UniqueIn f (Plus g h) if UniqueIn f g, In f h fails; UniqueIn f (Plus g h) if UniqueIn f h, In f g fails; UniqueIn f g fails" ]

----------------------------------------------------------------------------------------------------

even = ax "Even Z; Even (S n) if Odd n; Even n fails"
odd  = ax "Odd (S Z); Odd (S n) if Even n; Odd n fails"

evenf = ax "EvenF Z True; EvenF (S n) True if OddF n True; EvenF n False"
oddf  = ax "OddF (S n) True if EvenF n True; OddF n False"

evenOddFDs = [ ("EvenF", [[0] :~> [1]]), ("OddF", [[0] :~> [1]]) ]
evenOddAxs = [even, odd, evenf, oddf]