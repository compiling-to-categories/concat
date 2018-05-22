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

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- | Temporary "axiom" to let me type-check my experiments.
axiom :: String -> (u :- v)
axiom str = Sub (error (str ++ ": not verified"))

lePlusL :: forall a m n. (a <= m) :- (a <= m + n)
lePlusL = axiom "lePlusL"

lePlusR :: forall a m n. (a <= n) :- (a <= m + n)
lePlusR = axiom "lePlusR"

ltPlusL :: forall a m n. (a < m) :- (a < m + n)
ltPlusL = lePlusL @(a+1) @m @n

ltPlusR :: forall a m n. (a < n) :- (a < m + n)
ltPlusR = lePlusR @(a+1) @m @n

-- t6L :: forall a b c. (a <= b) :- (a <= b + c)
-- t6L = lePlusL @a @b @c

-- t6R :: forall a b c. (a <= c) :- (a <= b + c)
-- t6R = lePlusR @a @b @c

{--------------------------------------------------------------------
    Finite
--------------------------------------------------------------------}

data Finite n = forall a. (KnownNat a, a < n) => Finite (Proxy a)

-- -- In GADT notation
-- data Finite n where Finite :: (KnownNat a, a < n) => Proxy a -> Finite n

weakenFiniteL :: forall m n. Finite m -> Finite (m + n)
weakenFiniteL (Finite (Proxy :: Proxy a)) = Finite (Proxy @a) \\ ltPlusL @a @m @n

weakenFiniteR :: forall m n. Finite n -> Finite (m + n)
weakenFiniteR (Finite (Proxy :: Proxy a)) = Finite (Proxy @a) \\ ltPlusR @a @m @n

-- #define FProx(a) Finite (Proxy :: Proxy a)
-- weakenFiniteL (FProx(a)) = FProx(a) \\ ltPlusL @a @m @n

type KnownNat2 m n = (KnownNat m, KnownNat n)

sumToFin :: KnownNat2 m n => Finite m :+ Finite n -> Finite (m + n)
sumToFin = weakenFiniteL ||| weakenFiniteR

finToSum :: KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
finToSum = undefined
