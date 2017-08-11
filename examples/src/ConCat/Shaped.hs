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

import GHC.Generics hiding (S)

import ConCat.Nat
import ConCat.Pair

-- | Right-associated vector
type family RVec n where
  RVec Z     = U1
  RVec (S n) = Par1 :*: RVec n

-- | Left-associated vector
type family LVec n where
  LVec Z     = U1
  LVec (S n) = LVec n :*: Par1

-- | Right-associated functor exponentiation
type family RPow h n where
  RPow h Z     = Par1
  RPow h (S n) = h :.: RPow h n

-- | Left-associated functor exponentiation
type family LPow h n where
  LPow h Z     = Par1
  LPow h (S n) = LPow h n :.: h

type RBin n = RPow Pair n
type LBin n = LPow Pair n

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
