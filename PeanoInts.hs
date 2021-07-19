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
