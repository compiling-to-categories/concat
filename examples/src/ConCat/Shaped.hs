{-# LANGUAGE CPP  #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

-- | Vectors and functor exponentiations via type families.

module ConCat.Shaped (module ConCat.Shaped, module ConCat.Pair) where

import Data.Void (Void)
import GHC.Generics hiding (S)

import ConCat.Misc ((:+))
import ConCat.Nat
import ConCat.Pair

-- | Left-associated vector
type family LVec n where
  LVec Z     = U1
  LVec (S n) = LVec n :*: Par1

-- | Right-associated vector
type family RVec n where
  RVec Z     = U1
  RVec (S n) = Par1 :*: RVec n

-- | Left-associated functor exponentiation
type family LPow h n where
  LPow h Z     = Par1
  LPow h (S n) = LPow h n :.: h

-- | Right-associated functor exponentiation
type family RPow h n where
  RPow h Z     = Par1
  RPow h (S n) = h :.: RPow h n

type LBin n = LPow Pair n
type RBin n = RPow Pair n

-- Bushy binary leaf trees
type family Bush n where
  Bush Z     = Pair
  Bush (S n) = Bush n :.: Bush n

-- We can generalize from Pair and from squaring.

-- Bushy binary trees with data at branchings
type family Bush' n where
  Bush' Z     = U1
  Bush' (S n) = Par1 :*: (Bush' n :.: Bush' n)

-- I adapted Bush' from *Nested Datatypes* by Richard Bird and Lambert Meertens
-- (1998), <http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.184.8120>,
-- "data Bush a = NilB | ConsB a (Bush (Bush a))", adding depth-indexing. It
-- works fine for maps, folds, traversals, and scans. The use of (:*:) thwarts
-- FFT.

-- | @[0..n-1]@, left version
type family LFin n where
  LFin Z = Void
  LFin (S n) = LFin n :+ ()

-- | @[0..n-1]@, right version
type family RFin n where
  RFin Z = Void
  RFin (S n) = () :+ RFin n

#if 0

-- Functor versions

-- | @[0..n-1]@, left version
type family LFin' n where
  LFin' Z = V1
  LFin' (S n) = LFin' n :+: U1

-- | @[0..n-1]@, right version
type family RFin' n where
  RFin' Z = V1
  RFin' (S n) = U1 :+: RFin' n
#endif
