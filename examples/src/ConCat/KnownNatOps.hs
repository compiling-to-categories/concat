{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, KindSignatures,
             MultiParamTypeClasses, ScopedTypeVariables,
             TypeApplications, TypeFamilies, TypeOperators,
             UndecidableInstances,
             CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Some type families to be used with GHC.KnownNat.Solver

module ConCat.KnownNatOps where

import GHC.TypeLits
import GHC.TypeLits.KnownNat
import Data.Proxy
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
#else
import ConCat.Misc (natValAt)
#endif

-- When the plugin works with GHC 8.4 (base 4.11.0.0), get Div and Mod from
-- GHC.TypeNat instead of declaring here.
type family Div (m :: Nat) (n :: Nat) :: Nat
type family Mod (m :: Nat) (n :: Nat) :: Nat

instance (KnownNat a, KnownNat b) => KnownNat2 "Div" a b where
  natSing2 = SNatKn $ fromIntegral $ (div (natVal (Proxy ::  Proxy a)) (natVal (Proxy :: Proxy b)))
  {-# INLINE natSing2 #-}

instance (KnownNat a, KnownNat b) => KnownNat2 "Mod" a b where
  natSing2 = SNatKn $  fromIntegral $ (mod (natVal (Proxy ::  Proxy a)) (natVal (Proxy :: Proxy b)))
  {-# INLINE natSing2 #-}


