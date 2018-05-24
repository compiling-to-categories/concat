{-# LANGUAGE PatternSynonyms #-}
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

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin TypeNatSolver #-}
-- {-# OPTIONS_GHC -fconstraint-solver-iterations=100 #-}

-- | An alternative to Data.Finite from finite-typelits.
-- This version relies on GHC to verify all type arithmetic.
module ConCat.Fin where

import Data.Proxy (Proxy(..))
import GHC.TypeLits
import Data.Type.Bool
import Control.Arrow ((|||))

-- Experimental
import Data.Constraint

import ConCat.Misc ((:*),(:+),natValAt)

-- Missing from GHC.TypeLits
infix 4 <, >=, >
type a <  b = a + 1 <= b
type a >= b = b <= a
type a >  b = b < a

{--------------------------------------------------------------------
    Comparisons with evidence
--------------------------------------------------------------------}

-- | Result of 'compare' with evidence
data CompareEv u v
  = (u < v) => CompareLT
  | (u ~ v) => CompareEQ
  | (u > v) => CompareGT

compareEv :: forall u v. KnownNat2 u v => CompareEv u v
compareEv = error "compareEv: not defined"

-- compareEv = case natValAt @u `compare` natValAt @v of
--               LT -> CompareLT
--               EQ -> CompareEQ
--               GT -> CompareGT

-- Doesn't type-check, since compare doesn't produce *evidence*.

-- Alternative interface

compareEv' :: KnownNat2 u v =>
  ((u < v) => z) -> ((u ~ v) => z) -> ((u > v) => z) -> z
compareEv' = error "compareEv': not defined"

-- (<=) with evidence
data LeEv u v = (u <= v) => LeT | (u > v) => LeF

leEv :: forall u v. KnownNat2 u v => LeEv u v
leEv = case compareEv @u @v of
         CompareLT -> LeT
         CompareEQ -> LeT
         CompareGT -> LeF

-- (<) with evidence
data LtEv u v = (u < v) => LtT | (u >= v) => LtF

ltEv :: forall u v. KnownNat2 u v => LtEv u v
ltEv = case compareEv @u @v of
         CompareLT -> LtT
         CompareEQ -> LtF
         CompareGT -> LtF

{--------------------------------------------------------------------
    Finite
--------------------------------------------------------------------}

data Finite n = forall a. (KnownNat a, a < n) => Finite (Proxy a)

-- -- In GADT notation
-- data Finite n where Finite :: (KnownNat a, a < n) => Proxy a -> Finite n

-- TODO: Do we really need 'KnownNat a' here? I think we will, in order to
-- extract a dynamic natural number for comparisons and arithmetic.

finite :: forall a n. (KnownNat a, a < n) => Finite n
finite = Finite (Proxy @a)

-- Blows the constraint reduction stack
-- 
-- pattern Fi :: forall a n. (KnownNat a, a < n) => Finite n
-- pattern Fi = Finite (Proxy :: Proxy a)

weakenL :: forall m n. Finite m -> Finite (m + n)
weakenL (Finite (Proxy :: Proxy a)) = Finite (Proxy @a)

-- Variation
weaken' :: forall u v. u <= v => Finite u -> Finite v
weaken' (Finite (Proxy :: Proxy a)) = Finite (Proxy @a)

weakenR :: forall m n. Finite n -> Finite (m + n)
weakenR (Finite (Proxy :: Proxy b)) = Finite (Proxy @b)

bumpR :: forall m n. KnownNat m => Finite n -> Finite (m + n)
bumpR (Finite (Proxy :: Proxy b)) = Finite (Proxy @(m + b))

type KnownNat2 m n = (KnownNat m, KnownNat n)

sumToFin :: KnownNat m => Finite m :+ Finite n -> Finite (m + n)
sumToFin = weakenL ||| bumpR

finToSum :: forall m n. KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
finToSum (Finite (Proxy :: Proxy a)) =
  case ltEv @a @m of
    LtT -> Left  (finite @a)
    LtF -> Right (finite @(a - m))

-- Alternative definition using leEv

finToSum' :: forall m n. KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
finToSum' (Finite (Proxy :: Proxy a)) =
  case leEv @m @a of
    LeF -> Left  (finite @a)
    LeT -> Right (finite @(a - m))
