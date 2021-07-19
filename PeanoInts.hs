{-# LANGUAGE NoImplicitPrelude #-}
-- Implementation of all Integers, not just natural numbers via the Peano axioms
-- Names in this file may clash with the defaults/built-ins in Haskell libraries,
-- but this file is for taking notes and doing homework and not use as a library
-- (for this reason no traits/typeclasses are even mentioned, to keep focus on
-- data and algorithm rather than grouping of said algorithms)
--
-- Some things have been ported (?) from Rust's Peano library

import Prelude (Show, undefined)

-- An integer can be 0, the successor of another integer (which may or may not
-- be zero), or the predecessor of another integer (which also may or may not be
-- zero)
--
-- See https://en.wikipedia.org/wiki/Recursive_definition (also called inductive
-- definition) for more details.
data Integer = Zero | Pred Integer | Succ Integer deriving Show

-- Only so that we can support equality/comparison between two integers
data Boolean = True | False deriving Show


-- simplify chains of Pred and Succ which should never be chained together in
-- canonical form
simplify :: Integer -> Integer
simplify (Pred (Succ n)) = simplify n
simplify (Succ (Pred n)) = simplify n
simplify (Succ n)        = Succ (simplify n)
simplify (Pred n)        = Pred (simplify n)
simplify n               = n

-- Given n get n - 1
pred :: Integer -> Integer
pred (Succ n) = n
pred n        = Pred n

-- Given n get n + 1
succ :: Integer -> Integer
succ (Pred n) = n
succ n        = Succ n

-- From here on in, all functions assume that they're working with the canonical
-- form of an integer. So for actual use, (or more likely, testing within ghci)
-- use `simplify` before calling these functions to avoid unexpected results

-- negate an integer
neg :: Integer -> Integer
neg Zero     = Zero
neg (Succ a) = Pred (neg a)
neg (Pred a) = Succ (neg a)

eq :: Integer -> Integer -> Boolean
eq Zero      Zero     = True

-- 0 is not equal to any nonzero integers
eq (Succ a)  Zero     = False
eq Zero     (Succ b)  = False
eq (Pred a)  Zero     = False
eq Zero     (Pred b)  = False

eq (Succ a) (Succ b)  = eq a b
eq (Pred a) (Pred b)  = eq a b
eq _        _         = False

-- 0 is not greater than all positive numbers and is greater than all negative numbers
-- `gt m n` is the syntactic equivalent of mathematical expression m > n
gt  Zero   (Succ a) = False
gt  Zero   (Pred a) = True
gt (Pred a) Zero    = False
gt (Succ a) Zero    = True
-- all positive numbers are greater than negative numbers
gt (Succ a) (Pred b) = True
gt (Pred a) (Succ b) = False
-- if you go to zero faster when unwrapping, you are not greater
gt (Succ a) (Succ b) = gt a b
-- if you go to zero faster when unwrapping, you are greater
gt (Pred a) (Pred b) = gt a b

-- same logic as `gt`, just flipped
lt  Zero   (Succ a) = True
lt  Zero   (Pred a) = False
lt (Pred a) Zero    = True
lt (Succ a) Zero    = False
lt (Succ a) (Pred b) = False
lt (Pred a) (Succ b) = True
lt (Succ a) (Succ b) = gt a b
lt (Pred a) (Pred b) = gt a b
