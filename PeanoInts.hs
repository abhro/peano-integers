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
simplify (Pred (Succ n)) = reduce n
simplify (Succ (Pred n)) = reduce n
simplify (Succ n)        = Succ (reduce n)
simplify (Pred n)        = Pred (reduce n)
simplify n               = n
