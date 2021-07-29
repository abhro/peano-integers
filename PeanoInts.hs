{-# LANGUAGE NoImplicitPrelude #-}
-- Implementation of all Integers, not just natural numbers via the Peano axioms
-- Names in this file may clash with the defaults/built-ins in Haskell libraries,
-- but this file is for taking notes and doing homework and not use as a library
-- (for this reason no traits/typeclasses are even mentioned, to keep focus on
-- data and algorithm rather than grouping of said algorithms)
--
-- Some things have been ported (?) from Rust's Peano library

import Prelude (Show, undefined, otherwise, Bool(True, False))

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
-- implementation detail: the number doesn't actually strictly need to be in
-- canonical form, it just flips all the `Succ`s and `Pred`s in its construction
-- stack and so the result is still the opposite of the input, with just as
-- convoluted a construction stack as the input's.
neg :: Integer -> Integer
neg Zero     = Zero
neg (Succ a) = Pred (neg a)
neg (Pred a) = Succ (neg a)

-- allow absolute value operations, |n|
abs :: Integer -> Integer
abs Zero     = Zero
abs (Pred a) = Succ (abs a)
abs n        = n

eq :: Integer -> Integer -> Bool
eq Zero      Zero     = True

-- 0 is not equal to any nonzero integers
eq (Succ a)  Zero     = False
eq Zero     (Succ b)  = False
eq (Pred a)  Zero     = False
eq Zero     (Pred b)  = False
-- strip away one layer of the stack and compare what's left
eq (Succ a) (Succ b)  = eq a b
eq (Pred a) (Pred b)  = eq a b
-- anything that's left implies (LHS positive, RHS negative) or
-- (LHS negative, RHS positive)
eq  m        n        = False

gt :: Integer -> Integer -> Bool
-- 0 is not greater than all positive numbers and is greater than all negative numbers
-- `gt m n` is the syntactic equivalent of mathematical expression m > n
gt  Zero   (Succ a)  = False
gt  Zero   (Pred a)  = True
gt (Pred a) Zero     = False
gt (Succ a) Zero     = True
-- all positive numbers are greater than negative numbers
gt (Succ a) (Pred b) = True
gt (Pred a) (Succ b) = False
-- if you go to zero faster when unwrapping, you are not greater
gt (Succ a) (Succ b) = gt a b
-- if you go to zero faster when unwrapping, you are greater
gt (Pred a) (Pred b) = gt a b

lt :: Integer -> Integer -> Bool
-- same logic as `gt`, just flipped
lt  Zero   (Succ a)  = True
lt  Zero   (Pred a)  = False
lt (Pred a) Zero     = True
lt (Succ a) Zero     = False
lt (Succ a) (Pred b) = False
lt (Pred a) (Succ b) = True
lt (Succ a) (Succ b) = gt a b
lt (Pred a) (Pred b) = gt a b

add :: Integer -> Integer -> Integer
add m    Zero  = m  -- additive identity
add Zero n     = n  -- additive identity
-- adding a positive number and a negative number
add (Pred a) (Succ b) = add a b
add (Succ a) (Pred b) = add a b
-- adding two positive numbers
add (Succ a) (Succ b) = add a (Succ (Succ b))
-- adding two negative numbers
add (Pred a) (Pred b) = add a (Pred (Pred b))

-- Good news, subtraction is closed under this data type :)
sub :: Integer -> Integer -> Integer
sub  m        Zero    = m
sub  Zero     n       = neg n
-- subtracting a negative number from yourself is just adding that number's
-- positive counterpart to yourself (n = Pred b)
sub  m       (Pred b) = add m (neg (Pred b))
-- subtract positive numbers off of you
sub (Succ a) (Succ b) = sub a b
sub (Pred a) (Succ b) = Pred (Pred (sub a b))
-- only after writing all this code above did I figure out that the following
-- was probably a better and more elegant way to implement subtraction
-- sub m n = add m (neg n)

mul :: Integer -> Integer -> Integer
mul m           Zero        = Zero
mul Zero        n           = Zero
mul (Succ Zero) n           = n -- multiplicative identity
mul m           (Succ Zero) = m -- multiplicative identity
mul (Succ a)    (Succ b)    = add (Succ a) (mul (Succ a) b)
-- Anything involving the negatives just gets delegated to the two positives
-- case. Suddenly I'm really glad I wrote `neg`
mul (Pred a)    (Pred b)    = mul (neg (Pred a)) (neg (Pred b))
mul (Succ a)    (Pred b)    = neg (mul (Succ a) (neg (Pred b)))
mul (Pred a)    (Succ b)    = mul (Succ b) (Pred a)

-- Truncated integer division
div :: Integer -> Integer -> Integer
div  m        Zero       = undefined -- panic. I'm not getting involved with Maybe
div  Zero     n          = Zero
div  m       (Succ Zero) = m -- multiplicative identity. for illustrative purposes only
-- div m         m       = Succ Zero
-- sign handling cases: turn them both positive and negate the output quotient
-- as needed
div (Pred a) (Pred b)    = div (neg (Pred a)) (neg (Pred b)) -- m < 0, n < 0
div (Pred a) (Succ b)    = neg (div (neg (Pred a)) (Succ b)) -- m < 0, n > 0
div (Succ a) (Pred b)    = neg (div (Succ a) (neg (Pred b))) -- m > 0, n < 0
div  m        n                                              -- m > 0, n > 0
    | lt m n             = Zero                     -- guards :(
    | otherwise          = Succ (div (sub m n) n)

quot :: Integer -> Integer -> Integer
quot = div

-- Get remainder r of dividing m by n. If q is the quotient, it should fulfill
-- the following: m = n×q + r
-- And so, the remainder should be negative if m is negative :(
rem :: Integer -> Integer -> Integer
-- naive approach: r = m - n×q
-- because div takes O(m/n) time and mul takes... who knows
rem m n = sub m (mul n (div m n))

-- The signum function. Just for fun
sgn :: Integer -> Integer
sgn Zero     = Zero
sgn (Pred _) = Pred Zero
sgn (Succ _) = Succ Zero

-- Quick naming of numbers from -9 to 9 inclusive
p1 = Succ Zero :: Integer
p2 = Succ p1   :: Integer
p3 = Succ p2   :: Integer
p4 = Succ p3   :: Integer
p5 = Succ p4   :: Integer
p6 = Succ p5   :: Integer
p7 = Succ p6   :: Integer
p8 = Succ p7   :: Integer
p9 = Succ p8   :: Integer
n1 = Pred Zero :: Integer
n2 = Pred n1   :: Integer
n3 = Pred n2   :: Integer
n4 = Pred n3   :: Integer
n5 = Pred n4   :: Integer
n6 = Pred n5   :: Integer
n7 = Pred n6   :: Integer
n8 = Pred n7   :: Integer
n9 = Pred n8   :: Integer
