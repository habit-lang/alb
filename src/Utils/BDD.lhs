This file provides a library for describing sets of bit strings, encoded via
binary decision diagrams (BDDs).  It is included here for use in static
analysis and compilation of bitdata types.  (Unlike some BDD libraries, we
don't attempt to introduce or maintain significant sharing between subtrees;
that might be useful for a general BDD library, but doesn't appear to be
important for the (relatively small) examples we find in this particular
application.)

> module Utils.BDD(Pat, Width, width,
>                  pAll, pNone, pNot, pAnd, pOr, pAnds, pOrs,
>                  pPadR, pPadL, pSplit, pSplits,
>                  pBool, pIntMod,
>                  pShiftL, pShiftR, pDropL, pDropR,
>                  pGreater, pGreaterEq, pLess, pLessEq,
>                  isAll, isNone, superset, willMatch) where

> import Printer.Common

-- Ordered binary decision diagrams --------------------------------------------

A binary decision diagram (BDD) is a binary tree that encodes a Boolean-valued
function over a collection of Boolean variables.  There are two kinds of leaf
node, T and F, corresponding to the functions that always return true or
always return false, respectively.  There are also nodes (ITE v t f) that
correspond to an If-Then-Else test on the value of the variable v: for uses of
the function where v is true, we return the value that is determined by the
left subtree t, otherwise we return the value that is determined by the right
subtree f.  In this implementation, we represent variables by integer
constants (which, in what follows, correspond to bit positions in a bitdata
value).

> type Var = Int
> data BDD = F | T | ITE Var BDD BDD
>            deriving (Eq,Show)

If we fix the order in which variables are mentioned as we descend the BDD,
then we can maintain BDDs in a canonical form that is referred to as an
Ordered BDD (OBDD).  This is important because it means that we can test for a
tautology (or, respectively, an absurdity), simply by looking for the BDD T
(or, respectively, F).  We ensure that the canonical form is maintained by
using the following "smart constructor", ite, in place of ITE, to ensure that
higher-numbered variables are tested first and that redundant tests and
subtrees are eliminated.

> ite       :: BDD -> BDD -> BDD -> BDD
> ite T t _  = t
> ite F _ e  = e
> ite c t e  = if t' == e' then t' else ITE x t' e'
>  where x   = maximum [ y | ITE y _ _ <- [c,t,e] ]
>        t'  = ite (with True  c) (with True  t) (with True  e)
>        e'  = ite (with False c) (with False t) (with False e)
>        with b (ITE y p q)
>          | x == y      = if b then p else q
>        with _ p        = p

-- Bit patterns ----------------------------------------------------------------

Our main interest is to use OBDDs as a means of representing the sets of bit
vectors.  For example, ITE 1 F (ITE 0 T F) represents the set of bit vectors
in which bit 1 is false and bit 0 is true, while ITE 3 F T represents the set
of bit vectors with a zero in bit 3.  (We use the convention that bit 0 is
always the least significant or rightmost bit.)

For our specific application, we want to represent sets in which all of the
bit vectors have the same width, which we will refer to as "Bit Patterns".  We
can accomplish this by pairing an integer width with a BDD structure as
follows:

> type Width = Int
> data Pat   = Pat { width :: Width, bdd :: BDD }
>              deriving Eq

To illustrate this, the following examples of Pat values build on the
BDD examples described previously:

  Pat 2 (ITE 1 F (ITE 0 T F))
    represents the singleton set {01}.

  Pat 3 (ITE 1 F (ITE 0 T F))
    represents the set {001, 101}, which we abbreviate as _01
    using the underscore as a wildcard.
                   
  Pat 4 (ITE 3 F T)
    represents the set {0000,0001,0010,0011,0100,0101,0110,0111},
    which we can abbreviate as 0___, again using underscore as a
    wildcard.

The following function provides a way to generate a printable summary of the
set of bit vectors of some given width that are described by a given BDD.  The
output uses the underscore as a wildcard, as in the examples above, and may
sometimes produce multiple output patterns, which is why the function returns
a list and not just a single String.

> showBits           :: Width -> BDD -> [String]
> showBits w T        = [replicate (fromIntegral w) '_']
> showBits _ F        = []
> showBits w f@(ITE v p q)
>   | w' > v          = [ '_' : x | x <- showBits w' f ]
>   | otherwise       = [ '0' : x | x <- showBits w' q ]
>                    ++ [ '1' : x | x <- showBits w' p ]
>     where w'        = w - 1

Note that this function attempts to use underscore abbreviations, and usually
works quite well in practice, but doesn't always generate the shortest
possible output.  Given that these strings are only used for debugging or
diagnostic purposes, we don't consider this to be a serious concern.

For convenience, we can also use showBits to provide instances of Show and
Printable for bit patterns:

> instance Show Pat where
>   show (Pat w b) = unlines (showBits w b)

> instance Printable Pat where
>   ppr (Pat w b) = align
>                 $ vcat
>                 $ map text
>                 $ case splitAt 10 (showBits w b) of
>                     (first, [])   -> first
>                     (first, rest) -> first ++ ["etc... (" ++ show (length rest) ++ " more lines)"]

Now we begin the process of defining a collection of primitives for
constructing interesting Pat values, starting with pAll and pNone, which
represent the full and empty sets, respectively, of bit vector with some given
width:

> pAll, pNone       :: Width -> Pat
> pAll n             = Pat n T             -- always match
> pNone n            = Pat n F             -- never match

As a special case, individual Booleans can be encoded as bit patterns with
width 1.

> pBool              :: Bool -> Pat {-1-}
> pBool False         = Pat 1 (ITE 0 F T)
> pBool True          = Pat 1 (ITE 0 T F)

Standard Boolean operators---including negation, conjunction, and
disjunction---are easily defined in terms of if-then-else, and correspond to
complement, intersection, and union of bit vector sets:

> pNot               :: Pat -> Pat
> pNot (Pat n p)      = Pat n (ite p F T)  -- match if argument does not match

> pAnd, pOr          :: Pat {-n-} -> Pat {-n-} -> Pat {-n-}

> pAnd (Pat m p) (Pat n q)
>   | m == n          = Pat m (ite p q F)   -- match if both patterns match
>   | otherwise       = error "pAnd" "Different widths"

> pOr (Pat m p) (Pat n q)
>   | m == n          = Pat m (ite p T q)   -- match if one of the pats matches
>   | otherwise       = error "pOr" "Different widths"

Note that the code for pAnd and pOr includes test to ensure that the two input
arguments have the same width, and will generate a runtime error if that
condition is violated.

Conjunction and disjunction are easily extended to arbitrary lists of bit
patterns using foldr:

> pAnds, pOrs        :: Width -> [Pat] -> Pat
> pAnds w ps          = foldr pAnd (pAll w) ps
> pOrs w ps           = foldr pOr (pNone w) ps

Bit patterns can be padded on either the left (most significant bits) or right
(least significant bits).  If b is a string of bits in the set that is
represented by pattern p, then 0...0b is a string in the set represented by
pPadL p m, and b0...0 is a string in the set represented by pPadR p m,
assuming that the 0...0 in each case is a string of m zero bits.

> pPadL, pPadR       :: Pat {-n-} -> {-m::-} Width -> Pat {-m+n-}
> pPadL (Pat n p) m   = Pat (m+n) p

> pPadR p 0           = p
> pPadR (Pat n p) m   = Pat (m+n) (up p)
>   where up (ITE x l r)  = ITE (x+m) (up l) (up r)
>         up t            = t

The pSplit p q pattern represents the set of bit vectors that are obtained by
concatenating elements from p (upper bits) with elements from q (lower bits).

> pSplit             :: Pat {-m-} -> Pat {-n-} -> Pat {-m+n-}
> pSplit p q          = (p `pPadR` width q) `pAnd` (q `pPadL` width p)

Again, we can extend this to a list of patterns using foldr:

> pSplits            :: [Pat] -> Pat
> pSplits ps          = foldr pSplit (pAll 0) ps

One nice application of pSplit appears in the pIntMod function, which constructs
a 2's complement representation for a given integer value as a bit pattern
modulo the specified width.

> pIntMod               :: {-n::-} Width -> Integer -> Pat {-n-}
> pIntMod 0 _            = pAll 0
> pIntMod n x            = pIntMod (n-1) (x `div` 2) `pSplit` pBool (odd x)

The pDropL and pDropR operators can be used to remove bits from either the
left or the right, respectively, of a given bit pattern.  The implementations
of these operators require some fairly subtle manipulations of the underlying
BDDs.

> pDropL, pDropR     :: Pat {-n-} -> {-m::-} Width -> Pat {-n-m-}
> pDropL (Pat n p) m
>   | m <= n          = Pat w' (trunc p)
>   | otherwise       = error "pDropL" "Dropped too much"
>   where w'                = n - m
>         trunc (ITE x l r)
>           | x >= w'       = trunc (ite l T r)
>         trunc t           = t

> pDropR (Pat n p) m
>   | m <= n          = Pat w' (trunc p)
>   | otherwise       = error "pDropR" "Dropped too much"
>   where w'                = n - m
>         trunc (ITE x l r)
>           | x >= m        = let l' = trunc l
>                                 r' = trunc r
>                             in if l' == r' then l' else ITE (x-m) l' r'
>           | otherwise     = T
>         trunc t           = t

The pShiftL and pShiftR operators correspond to the standard shift operations
on bit vectors.  A left shift removes some number of (most significant) bits
and adds is the same number of zero bits on the right.  A right shift removes
some number of (least significant) bits and adds in the same number of zero
bits on the left.  In both cases, the width of the original bit pattern is
preserved.

> pShiftL, pShiftR   :: Pat {-m-} -> Width -> Pat {-m-}
> pShiftL p n         = (p `pSplit` pIntMod n 0) `pDropL` n
> pShiftR p n         = (pIntMod n 0 `pSplit` p) `pDropR` n

There are four operators for describing bit patterns whose members,
interpreted as unsigned numbers are all greater than (pGreater), greater than
or equal (pGreaterEq), less than (pLess), or less than or equal (pLessEq) some
given integer.

> pGreater, pGreaterEq, pLess, pLessEq :: {-n::-} Width -> Integer -> Pat {-n-}
> pGreater   n l                          -- { s in Bit n | [[s]] >  l }
>    | l <  0    = pAll n
>    | l >= 2^n  = pNone n
>    | otherwise = pGreaterMod n l
> pGreaterEq n l = pGreater n (l-1)       -- { s in Bit n | [[s]] >= l }
> pLess      n l = pNot (pGreaterEq n l)  -- { s in Bit n | [[s]] <  l }
> pLessEq    n l = pNot (pGreater n l)    -- { s in Bit n | [[s]] <= l }

All of these comparison operators are defined (directly or indirectly) in
terms of the following comparison that works modulo the given bit width:

> pGreaterMod        :: {-n::-} Width -> Integer -> Pat {-n-}
> pGreaterMod 0 _     = pNone 0
> pGreaterMod n l     = (pGreaterMod n1 l2 `pSplit` pAll 1) `pOr` also
>   where
>         l2            = l `div` 2
>         n1            = n - 1
>         also
>           | even l    = pIntMod n1 l2 `pSplit` pBool True
>           | otherwise = pNone n


-- Testing bit patterns --------------------------------------------------------

The following functions exploit the canonical structure of OBDDs to determine
if a given bit pattern represents the set of all possible bit vectors of the
specified width or, conversely, if it represents the empty set.

> isAll            :: Pat -> Bool
> isAll (Pat _ T)   = True
> isAll _           = False

> isNone           :: Pat -> Bool
> isNone (Pat _ F)  = True
> isNone _          = False

The expression (p `superset` q) returns True if p is a superset of q when the
two bit patterns are interpreted as sets of bit vectors.

> superset          :: Pat -> Pat -> Bool
> p `superset` q     = isNone (q `pAnd` pNot p)

The expression (p `willMatch` n) returns True if the 2s complement of n is
included in the set represented by p.

> willMatch         :: Pat -> Integer -> Bool
> p `willMatch` n    = p `superset` pIntMod (width p) n

--------------------------------------------------------------------------------
