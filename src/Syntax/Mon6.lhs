----------------------------------------------------------------------------------------------------
-- Mon6: a simple monadic intermediate language.
--
-- Based on the similarly named language of January 2011.

> module Syntax.Mon6 (module Syntax.Common, module Syntax.Mon6) where

> import Data.Maybe (fromMaybe)
> import Data.Word
> import Syntax.Common
> import Syntax.XMPEG (Type(..))
> import qualified Utils.BDD as BDD

TODO: (from mon6.lhs)
- need a better way to figure out/handle top-level definitions

-- Abstract syntax for target language: --------------------------------------


> type Var  = Id                                -- variables
> type CFun = Id                                -- constructor functions
> type Name = Id


A compiled program is a collection of definitions:

> type Prog primimpl = [Defn primimpl]                   -- programs
> data Defn primimpl = BlockDefn   Name [Var] Code       -- basic block
>                    | ClosureDefn Name [Var] Var Tail   -- closure entry point
>                    | Init        Name Tail             -- top-level initializer
>                    | PrimDefn    Name primimpl         -- primitive definitions

[Invariant: The Tails in ClosureDefn should be ClosAllocs, CompAllocs, or
BlockCalls.]  TODO: why not DataAllocs too?

A basic block is described by a sequence of simple bind instructions
concluding with a tail call:

> data Code = Bind Var Tail Code                -- monadic bind
>           | Done Tail                         -- tail call
>           | Case Var [Alt] Tail               -- case analysis, with default
>           | BitCase Var [BAlt] Tail           -- bitwise case analysis, with default
> type Alt = (CFun, [Var], Tail)                -- alternative
> type BAlt = (BDD.Pat, Var, Tail)              -- bitwise alternative

[Invariant: The Tails in TAlt's should be BlockCalls.]

We use the term "tail call" in a slightly more general sense than usual
to describe any basic expression that might be used in the tail position
of a code block, including all of the following cases:

> data Atom = Var Var | Const Word

TODO: should the 'Var's in BlockCall, DataAlloc, and ClosAlloc be Atoms?

> data Tail = Return Atom                       -- simple return
>           | BlockCall Name [Var]              -- branch to a block
>           | DataAlloc CFun [Var]              -- allocate data
>           | ClosAlloc Name [Var]              -- allocate a closure
>           | Enter Var Var                     -- enter a closure
>           | PrimCall Name [Var]               -- invoke a primitive

> instance HasVariables Tail
>     where freeVariables (Return (Var v))   = [v]
>           freeVariables (Return (Const b)) = []
>           freeVariables (BlockCall _ vs)   = vs
>           freeVariables (DataAlloc _ vs)   = vs
>           freeVariables (ClosAlloc _ vs)   = vs
>           freeVariables (Enter v w)        = [v, w]
>           freeVariables (PrimCall _ vs)    = vs

>           rename s (Return (Var v))    = Return (Var (replacement s v))
>           rename s (Return (Const b))  = Return (Const b)
>           rename s (BlockCall name vs) = BlockCall name (replacements s vs)
>           rename s (DataAlloc ctor vs) = DataAlloc ctor (replacements s vs)
>           rename s (ClosAlloc name vs) = ClosAlloc name (replacements s vs)
>           rename s (Enter v w)         = Enter (replacement s v) (replacement s w)
>           rename s (PrimCall p vs)     = PrimCall p (replacements s vs)

> instance HasVariables Code
>     where freeVariables (Bind v t c)         = filter (v /=) (freeVariables c) ++ freeVariables t
>           freeVariables (Done t)             = freeVariables t
>           freeVariables (Case v alts def)    = v : concat [filter (`notElem` vs) (freeVariables a) | (_, vs, a) <- alts] ++ freeVariables def
>           freeVariables (BitCase x alts def) = x : concat [filter (y /=) (freeVariables a) | (_, y, a) <- alts] ++ freeVariables def

>           rename s (Bind v t c)         = Bind v (rename s t) (rename (filter ((v ==) . fst) s) c)
>           rename s (Done t)             = Done (rename s t)
>           rename s (Case v alts def)    = Case (replacement s v) [(ctor, vs, rename (filter ((`notElem` vs) . fst) s) a) | (ctor, vs, a) <- alts] (rename s def)
>           rename s (BitCase x alts def) = BitCase (replacement s x) [(ctor, y, rename (filter ((y /=) . fst) s) a) | (ctor, y, a) <- alts] (rename s def)
