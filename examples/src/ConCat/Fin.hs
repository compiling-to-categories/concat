{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE AllowAmbiguousTypes #-} -- for temporary "axioms"

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

--   Unable to resolve module looked up by plugin:
-- Proof.Propositional.Empty


-- | An alternative to Data.Finite from finite-typelits.
-- This version relies on GHC to verify all type arithmetic.

module ConCat.Fin where

import Data.Proxy (Proxy(..))
import GHC.TypeLits
import Control.Arrow ((|||))

-- Experimental
import Data.Constraint

import ConCat.Misc ((:+))

-- Missing from GHC.TypeLits
infix 4 <, >=, >
type a <  b = a + 1 <= b
type a >= b = b <= a
type a >  b = b < a

data Finite n = forall a. (KnownNat a, a < n) => Finite (Proxy a)

-- -- Same in GADT notation
-- data Finite n where
--   Finite :: (KnownNat a, a < n) => Proxy a -> Finite n

type KnownNat2 m n = (KnownNat m, KnownNat n)

sumToFin :: KnownNat2 m n => Finite m :+ Finite n -> Finite (m + n)
sumToFin = weakenFiniteL ||| weakenFiniteR

-- With better constraint solving, we could replace weakenL and weakenR with the following:
-- 
-- sumToFin :: forall m n. KnownNat2 m n => Finite m :+ Finite n -> Finite (m + n)
-- sumToFin (Left  (Finite (Proxy :: Proxy a))) = Finite (Proxy :: Proxy a)
-- sumToFin (Right (Finite (Proxy :: Proxy a))) = Finite (Proxy :: Proxy (m + a))

finToSum :: KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
finToSum = undefined


{- 

src/ConCat/Fin.hs:47:48-72: error: …
    • Could not deduce: ((a + 1) <=? (m + n)) ~ 'True
        arising from a use of ‘Finite’
      from the context: (KnownNat a, (a + 1) <= m)
        bound by a pattern with constructor:
                   Finite :: forall (n :: Nat) (a :: Nat).
                             (KnownNat a, (a + 1) <= n) =>
                             Proxy a -> Finite n,
                 in an equation for ‘finToSum’
    • In the expression: Finite (Proxy :: Proxy a)
      In an equation for ‘finToSum’:
          finToSum (Left (Finite (Proxy :: Proxy a)))
            = Finite (Proxy :: Proxy a)

src/ConCat/Fin.hs:48:48-78: error: …
    • Could not deduce: (((m + a) + 1) <=? (m + n)) ~ 'True
        arising from a use of ‘Finite’
      from the context: (KnownNat a, (a + 1) <= n)
        bound by a pattern with constructor:
                   Finite :: forall (n :: Nat) (a :: Nat).
                             (KnownNat a, (a + 1) <= n) =>
                             Proxy a -> Finite n,
                 in an equation for ‘finToSum’
    • In the expression: Finite (Proxy :: Proxy (m + a))
      In an equation for ‘finToSum’:
          finToSum (Right (Finite (Proxy :: Proxy a)))
            = Finite (Proxy :: Proxy (m + a))

-}

-- Simpler example

-- data AtMost n = forall a. (KnownNat a, a <= n) => AtMost (Proxy a)

-- foo :: AtMost n -> AtMost (n + 1)
-- foo (AtMost (Proxy :: Proxy a)) = AtMost (Proxy :: Proxy a)

{-

    • Could not deduce: (a <=? (n + 1)) ~ 'True
        arising from a use of ‘AtMost’
      from the context: (KnownNat a, a <= n)
        bound by a pattern with constructor:
                   AtMost :: forall (n :: Nat) (a :: Nat).
                             (KnownNat a, a <= n) =>
                             Proxy a -> AtMost n,
                 in an equation for ‘foo’
        at /Users/conal/Haskell/concat/classes/src/ConCat/Fin.hs:89:6-30
    • In the expression: AtMost (Proxy :: Proxy a)
      In an equation for ‘foo’:
          foo (AtMost (Proxy :: Proxy a)) = AtMost (Proxy :: Proxy a)
    • Relevant bindings include
        foo :: AtMost n -> AtMost (n + 1)
          (bound at /Users/conal/Haskell/concat/classes/src/ConCat/Fin.hs:89:1)

-}

{-
-- Some experiments (requiring AllowAmbiguousTypes)

t1 :: (a <= n) :- (a <= n + m)
t1 = Sub Dict
-- Could not deduce: (a <=? (n + m)) ~ 'True from the context: a <= n

t2 :: Dict (n <= n + m)
t2 = Dict
-- Couldn't match type ‘n <=? (n + m)’ with ‘'True’

t3 :: Dict (0 <= n)
t3 = Dict
-- Fine

t4 :: Dict (1 <= n)
t4 = Dict
-- Couldn't match type ‘1 <=? n’ with ‘'True’ [as expected]

-}

-- | Temporary "axiom" to let me type-check my experiments.
axiom :: String -> (u :- v)
axiom str = Sub (error (str ++ ": not verified"))

lePlusL :: forall a m n. (a <= m) :- (a <= m + n)
lePlusL = axiom "lePlusL"

lePlusR :: forall a m n. (a <= n) :- (a <= m + n)
lePlusR = axiom "lePlusR"

leLessPlusL :: forall m n. () :- (m <= m + n)
leLessPlusL = axiom "leLessPlus"

-- leLessPlusL = lePlusL @0 @m @n
-- 
--   Couldn't match type ‘(0 <=? m) ~ 'True’ with ‘() :: Constraint’
--   Expected type: (() :: Constraint) :- (m <= (m + n))
--     Actual type: (0 <= m) :- (0 <= (m + n))

ltPlusL :: forall a m n. (a < m) :- (a < m + n)
ltPlusL = lePlusL @(a+1) @m @n

ltPlusR :: forall a m n. (a < n) :- (a < m + n)
ltPlusR = lePlusR @(a+1) @m @n

t5 :: forall a b. () :- (a <= a + b)
t5 = leLessPlusL @a @b

t6L :: forall a b c. (a <= b) :- (a <= b + c)
t6L = lePlusL @a @b @c

t6R :: forall a b c. (a <= c) :- (a <= b + c)
t6R = lePlusR @a @b @c

data AtMost n = forall a. (KnownNat a, a <= n) => AtMost (Proxy a)

weakenAtMostL :: forall m n. AtMost m -> AtMost (m + n)
weakenAtMostL (AtMost (Proxy :: Proxy a)) = AtMost (Proxy @a) \\ lePlusL @a @m @n

weakenAtMostR :: forall m n. AtMost n -> AtMost (m + n)
weakenAtMostR (AtMost (Proxy :: Proxy a)) = AtMost (Proxy @a) \\ lePlusR @a @m @n

weakenFiniteL :: forall m n. Finite m -> Finite (m + n)
weakenFiniteL (Finite (Proxy :: Proxy a)) = Finite (Proxy @a) \\ ltPlusL @a @m @n

weakenFiniteR :: forall m n. Finite n -> Finite (m + n)
weakenFiniteR (Finite (Proxy :: Proxy a)) = Finite (Proxy @a) \\ ltPlusR @a @m @n
