{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, KindSignatures,
             MultiParamTypeClasses, ScopedTypeVariables, TemplateHaskell,
             TypeApplications, TypeFamilies, TypeOperators,
             UndecidableInstances,
             CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Some type families to be used with GHC.KnownNat.Solver

module ConCat.KnownNatOps where

import GHC.TypeLits
import GHC.TypeLits.KnownNat
import ConCat.Misc (natValAt)

#define Op2(Fam,op) \
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''Fam) a b where { \
  natSing2 = SNatKn (op (natValAt @a) (natValAt @b)) ; \
  {-# INLINE natSing2 #-} ; \
  }

-- When the plugin works with GHC 8.4 (base 4.11.0.0), get Div and Mod from
-- GHC.TypeNat instead of declaring here.
type family Div (m :: Nat) (n :: Nat) :: Nat
type family Mod (m :: Nat) (n :: Nat) :: Nat

Op2(Div,div)
Op2(Mod,mod)
