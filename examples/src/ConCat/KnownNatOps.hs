{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, KindSignatures,
             MultiParamTypeClasses, ScopedTypeVariables, TemplateHaskell,
             TypeApplications, TypeFamilies, TypeOperators,
             UndecidableInstances,
             CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Some type families to be used with GHC.KnownNat.Solver

module ConCat.KnownNatOps where

import Data.Proxy            (Proxy (..))
import GHC.TypeLits

import GHC.TypeLits.KnownNat

#define Op2(Fam,op) \
type family Fam (m :: Nat) (n :: Nat) :: Nat ; \
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''Fam) a b where { \
  natSing2 = SNatKn (op (natVal (Proxy @a)) (natVal (Proxy @b))) ; \
  {-# INLINE natSing2 #-} ; \
  }
   
#if 1

Op2(Div,div)
Op2(Mod,mod)

#else

-- Swiped from GHC.TypNats in base 4.11.0.0
type family Div (m :: Nat) (n :: Nat) :: Nat
type family Mod (m :: Nat) (n :: Nat) :: Nat

-- See http://hackage.haskell.org/package/ghc-typelits-knownnat/docs/GHC-TypeLits-KnownNat.html

instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''Div) a b where
  natSing2 = SNatKn (natVal (Proxy @a) `div` natVal (Proxy @b))
  {-# INLINE natSing2 #-}

instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''Mod) a b where
  natSing2 = SNatKn (natVal (Proxy @a) `mod` natVal (Proxy @b))
  {-# INLINE natSing2 #-}

#endif
