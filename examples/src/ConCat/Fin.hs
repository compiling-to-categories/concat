{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE CPP #-}
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

#define SMT_NATS

#ifdef SMT_NATS
{-# OPTIONS_GHC -fplugin TypeNatSolver #-}
#endif

-- -- Unable to resolve module looked up by plugin: Proof.Propositional.Empty
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}


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

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- Inference rules for inequalities. Unnecessary with TypeNatSolver

#ifndef SMT_NATS
-- | Temporary "axiom" to let me type-check my experiments.
axiom :: String -> (u :- v)
axiom str = Sub (error (str ++ ": not verified"))
#endif

lePlusL :: forall a m n. (a <= m) :- (a <= m + n)
lePlusR :: forall a m n. (a <= n) :- (a <= m + n)

#ifdef SMT_NATS
lePlusL = Sub Dict
lePlusR = Sub Dict
#else
lePlusL = axiom "lePlusL"
lePlusR = axiom "lePlusR"
#endif

ltPlusL :: forall a m n. (a < m) :- (a < m + n)
ltPlusL = lePlusL @(a+1) @m @n

ltPlusR :: forall a m n. (a < n) :- (a < m + n)
ltPlusR = lePlusR @(a+1) @m @n

-- t6L :: forall a b c. (a <= b) :- (a <= b + c)
-- t6L = lePlusL @a @b @c

-- t6R :: forall a b c. (a <= c) :- (a <= b + c)
-- t6R = lePlusR @a @b @c

lePlus2L :: forall a m n. (a <= m) :- (a + n <= m + n)
lePlus2R :: forall b m n. (b <= n) :- (m + b <= m + n)
ltPlus2L :: forall a m n. (a <  m) :- (a + n <  m + n)
ltPlus2R :: forall b m n. (b <  n) :- (m + b <  m + n)

#ifdef SMT_NATS
lePlus2L = Sub Dict
lePlus2R = Sub Dict
ltPlus2L = Sub Dict
ltPlus2R = Sub Dict
#else
lePlus2L = axiom "lePlus2L"
lePlus2R = axiom "lePlus2R"
ltPlus2L = axiom "ltPlus2L"
ltPlus2R = axiom "ltPlus2R"
#endif

-- For lePlus2L @(a+1) @m @n:
-- 
--   Couldn't match type ‘((a + 1) + n) <=? (m + n)’
--                  with ‘((a + n) + 1) <=? (m + n)’

infixl 1 <+
#ifdef SMT_NATS
(<+) :: (a => r) -> (a :- b) -> (a => r)
q <+ _ = q
#else
(<+) :: (b => r) -> (a :- b) -> (a => r)
(<+) = (\\)
#endif

{--------------------------------------------------------------------
    Finite
--------------------------------------------------------------------}

data Finite n = forall a. (KnownNat a, a < n) => Finite (Proxy a)

-- -- In GADT notation
-- data Finite n where Finite :: (KnownNat a, a < n) => Proxy a -> Finite n

finite :: forall a n. (KnownNat a, a < n) => Finite n
finite = Finite (Proxy @a)

zero :: (KnownNat n, 0 < n) => Finite n
zero = finite @0

weakenL :: forall m n. Finite m -> Finite (m + n)
weakenL (Finite (Proxy :: Proxy a)) = Finite (Proxy @a) <+ ltPlusL @a @m @n

weakenR :: forall m n. Finite n -> Finite (m + n)
weakenR (Finite (Proxy :: Proxy b)) = Finite (Proxy @b) <+ ltPlusR @b @m @n

-- bumpR :: forall m n. Finite n -> Finite (m + n)
-- bumpR (Finite (Proxy :: Proxy b)) = Finite (Proxy @b) <+ ltPlus2R @b @m @n

-- #define FProx(a) Finite (Proxy :: Proxy a)
-- weakenL (FProx(a)) = FProx(a) <+ ltPlusL @a @m @n

type KnownNat2 m n = (KnownNat m, KnownNat n)

sumToFin :: KnownNat2 m n => Finite m :+ Finite n -> Finite (m + n)
sumToFin = weakenL ||| weakenR

finToSum :: KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
finToSum = undefined

-- Subtraction

data Diff u v = (u >= v) => Diff (Proxy (u - v))

sub :: forall u v. KnownNat2 u v => Diff u v :+ Diff v u
sub = undefined
