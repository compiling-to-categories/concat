{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE AllowAmbiguousTypes #-} -- for temporary "axioms"

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- -- Allows eliminating some uses of assumeFinite.
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

-- | An alternative to Data.Finite from finite-typelits.
-- This version relies on GHC to verify type arithmetic where possible.
module ConCat.Finite where

import Data.Proxy (Proxy(..))
import GHC.TypeLits
import Data.Type.Equality
import Data.Type.Bool
import Control.Arrow ((|||))
import Unsafe.Coerce (unsafeCoerce)

import Data.Constraint

import ConCat.Misc ((:*),(:+),natValAt)
import ConCat.KnownNatOps (Div, Mod)

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

infix 1 |-
-- | A synonym for '(:-)' but with a looser fixity.
type (|-) = (:-)

infix 4 >=?
type a >=? b = b <=? a

infix 4 <?, >?, <, >=, >
type a <? b = a + 1 <=? b
type a >? b = b <? a
type a <  b = (a <? b) ~ 'True
type a >= b = b <= a
type a >  b = b < a

unsafeEqual :: forall a b. a :~: b
unsafeEqual = unsafeCoerce Refl

unsafeWithEQ :: forall a b r. (a ~ b => r) -> r
unsafeWithEQ r | Refl <- unsafeEqual @a @b = r

unsafeWithTrue :: forall a r. (a ~ 'True => r) -> r
unsafeWithTrue r | Refl <- unsafeEqual @a @'True = r

axiom :: forall p q. p ~ 'True |- q ~ 'True
axiom | Refl <- unsafeEqual @q @'True = Sub Dict

type KnownNat2 m n = (KnownNat m, KnownNat n)

{--------------------------------------------------------------------
    Comparisons with evidence
--------------------------------------------------------------------}

-- | Result of 'compare' with evidence
data CompareEv u v = (u < v) => CompareLT
                   | (u ~ v) => CompareEQ
                   | (u > v) => CompareGT

-- 'compare' plus evidence
compareEv :: forall u v. KnownNat2 u v => CompareEv u v
compareEv = case natValAt @u `compare` natValAt @v of
              LT -> unsafeWithTrue @(u <? v) CompareLT
              EQ -> unsafeWithEQ   @u    @v  CompareEQ
              GT -> unsafeWithTrue @(u >? v) CompareGT

-- Alternative interface
compareEv' :: forall u v z. KnownNat2 u v =>
  ((u < v) => z) -> ((u ~ v) => z) -> ((u > v) => z) -> z
compareEv' lt eq gt = case compareEv @u @v of
                        CompareLT -> lt
                        CompareEQ -> eq
                        CompareGT -> gt

-- (<) with evidence
data LtEv u v = (u < v) => LtT | (u >= v) => LtF

ltEv :: forall u v. KnownNat2 u v => LtEv u v
ltEv = case compareEv @u @v of
         CompareLT -> LtT
         CompareEQ -> LtF
         CompareGT -> unsafeWithTrue @(u >=? v) LtF

-- (<=) with evidence
data LeEv u v = (u <= v) => LeT | (u > v) => LeF

leEv :: forall u v. KnownNat2 u v => LeEv u v
leEv = case compareEv @u @v of
         CompareLT -> unsafeWithTrue @(u <=? v) LeT
         CompareEQ -> LeT
         CompareGT -> LeF

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

-- Assume correctly bounded
assumeFinite' :: forall a m. KnownNat a => Finite m
assumeFinite' = unsafeWithTrue @(a <? m) (finite @a)

-- | Assume correctly bounded but with an explicit, checked premise. Use only
-- when @p |- a < m@. The type arguments @p@ and @a@ must be given explicitly,
-- but usually @m@ can be inferred from context.
assumeFinite :: forall p a m. (KnownNat a, p) => Finite m
assumeFinite = assumeFinite' @a @m

weakenL :: forall m n. Finite m -> Finite (m + n)
weakenL (Finite (Proxy :: Proxy a)) = finite @a \\ axiom @(a <? m) @(a <? m + n)
                                      -- assumeFinite @(a < m) @a

-- Variation
weaken' :: forall u v. u <= v => Finite u -> Finite v
weaken' (Finite (Proxy :: Proxy a)) = assumeFinite @(a < u) @a

weakenR :: forall m n. Finite n -> Finite (m + n)
weakenR (Finite (Proxy :: Proxy b)) = assumeFinite @(b < n) @b

bumpR :: forall m n. KnownNat m => Finite n -> Finite (m + n)
bumpR (Finite (Proxy :: Proxy b)) = assumeFinite @(b < n) @(m + b)

sumToFin :: KnownNat m => Finite m :+ Finite n -> Finite (m + n)
sumToFin = weakenL ||| bumpR

finToSum :: forall m n. KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
finToSum (Finite (Proxy :: Proxy c)) =
  case ltEv @c @m of
    LtT -> Left  (finite @c)
    LtF -> Right (assumeFinite @(c < m + n) @(c - m))

#if 0

-- Look for duality between sumToFin and finToSum.

-- With some inlining
sumToFin' :: forall m n. KnownNat m => Finite m :+ Finite n -> Finite (m + n)
sumToFin' =
  (\ (Finite (Proxy :: Proxy a)) -> Finite (Proxy :: Proxy    a   )) |||
  (\ (Finite (Proxy :: Proxy b)) -> Finite (Proxy :: Proxy (m + b)))

finToSum'' :: forall m n. KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
finToSum'' (Finite (Proxy :: Proxy c)) =
  case ltEv @c @m of
    LtT -> Left  (Finite (Proxy :: Proxy    c   ))
    LtF -> Right (Finite (Proxy :: Proxy (c - m)))

#endif

finToProd :: forall m n. KnownNat n => Finite m :* Finite n -> Finite (m * n)
finToProd (Finite (Proxy :: Proxy a), Finite (Proxy :: Proxy b)) =
  assumeFinite @(a < m, b < n) @(a * n + b)

prodToFin :: forall m n. KnownNat n => Finite (m * n) -> Finite m :* Finite n
prodToFin (Finite (Proxy :: Proxy c)) =
  ( assumeFinite @(c < m * n) @(c `Div` n) @m
  , assumeFinite @(c < m * n) @(c `Mod` n) @n )
