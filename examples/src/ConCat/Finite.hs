{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
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

import Prelude hiding (id,(.))

import Data.Proxy (Proxy(..))
import GHC.TypeLits
-- import GHC.Natural (Natural)
import Data.Type.Equality
import Data.Type.Bool
import Control.Arrow ((|||))
import Unsafe.Coerce (unsafeCoerce)

import Data.Constraint (Dict(..),(:-)(..),(\\))
import qualified Data.Finite as TF
import qualified Data.Finite.Internal as TF
import Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as V
import Data.Functor.Rep (index)
import Control.Newtype

import ConCat.Misc ((:*),(:+),natValAt,cond,inNew)
import ConCat.KnownNatOps (Div, Mod)
import ConCat.Isomorphism
import ConCat.AltCat (id,(.),(***),(+++))

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

axiom :: forall p q. p |- q ~ 'True
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
              EQ -> unsafeWithEQ    @u   @v  CompareEQ
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

finVal :: Finite n -> Integer  -- Natural?
finVal (Finite p) = natVal p

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
-- assumeFinite = assumeFinite' @a @m
assumeFinite = finite @a \\ axiom @p @(a <? m)

weakenL :: forall m n. Finite m -> Finite (m + n)
weakenL (Finite (Proxy :: Proxy a)) = -- finite @a \\ axiom @(a < m) @(a <? m + n)
                                      assumeFinite @(a < m) @a

-- Variation
weaken' :: forall u v. u <= v => Finite u -> Finite v
weaken' (Finite (Proxy :: Proxy a)) = -- finite @a \\ axiom @(a < u) @(a <? v)
                                      assumeFinite @(a < u) @a

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

prodToFin :: forall m n. KnownNat n => Finite m :* Finite n -> Finite (m * n)
prodToFin (Finite (Proxy :: Proxy a), Finite (Proxy :: Proxy b)) =
  assumeFinite @(a < m, b < n) @(a * n + b)

finToProd :: forall m n. KnownNat n => Finite (m * n) -> Finite m :* Finite n
finToProd (Finite (Proxy :: Proxy c)) =
  ( assumeFinite @(c < m * n) @(c `Div` n) @m
  , assumeFinite @(c < m * n) @(c `Mod` n) @n )

finSum :: KnownNat2 m n => Finite m :+ Finite n <-> Finite (m + n)
finSum = Iso sumToFin finToSum

finProd :: KnownNat2 m n => Finite m :* Finite n <-> Finite (m * n)
finProd = Iso prodToFin finToProd

{----------------------------------------------------------------------
   A class of types with known finite representations.
----------------------------------------------------------------------}

class KnownNat (Card a) => HasFin a where
  type Card a :: Nat
  finI :: a <-> Finite (Card a)

instance KnownNat n => HasFin (Finite n) where
  type Card (Finite n) = n
  finI = id

instance HasFin () where
  type Card () = 1
  finI = Iso (const (finite @0)) (const ())

instance HasFin Bool where
  type Card Bool = 2
  finI = Iso (cond (finite @0) (finite @1)) ((> 0) . finVal)

instance (HasFin a, HasFin b) => HasFin (a :+ b) where
  type Card (a :+ b) = Card a + Card b
  finI = finSum . (finI +++ finI)

instance (HasFin a, HasFin b) => HasFin (a :* b) where
  type Card (a :* b) = Card a * Card b
  finI = finProd . (finI *** finI)

-- instance (HasFin a, HasFin b) => HasFin (a :^ b) where
--   type Card (a :^ b) = Card a ^ Card b
--   finI = finExp . Iso liftFin inFin

{----------------------------------------------------------------------
  Domain-typed "arrays"
----------------------------------------------------------------------}

newtype Arr a b = Arr (Vector (Card a) b)

instance Newtype (Arr a b) where
  type O (Arr a b) = Vector (Card a) b
  pack v = Arr v
  unpack (Arr v) = v

instance Functor (Arr a) where
  fmap = inNew . fmap

-- (!) :: HasFin a => Arr a b -> (a -> b)
-- Arr v ! a = v `index` isoFwd finI a

-- Oops. The Representable (Vector n) instance in Orphans currently uses Finite
-- from finite-typelits. To fix, I'll have to move the Finite type to
-- concat/classes and import in Orphans. At some point, the vector-sized library
-- may add a conflicting instance (I would), and we'll probably have to make our
-- own vector-sized variant. The CPU implementation could still be built on
-- unsized vectors.

(!) :: HasFin a => Arr a b -> (a -> b)
Arr v ! a = v `vindex` isoFwd finI a

toTFinite :: KnownNat n => Finite n -> TF.Finite n
toTFinite = TF.Finite . finVal

toFinite :: KnownNat n => TF.Finite n -> Finite n
toFinite _ = error "toFinite: not yet defined"

-- Is it possible to define toFinite? How to synthesize (KnownNat a, a < n)?
-- Maybe via magicDict as in withSNat in GHC.TypeNat.

vindex :: KnownNat n => Vector n a -> (Finite n -> a)
vindex v = index v . toTFinite
-- v `vindex` i = v `index` toTFinite i

vtabulate :: KnownNat n => (Finite n -> a) -> Vector n a
vtabulate f = V.generate (f . toFinite)
-- vtabulate = V.generate . (. toFinite)
