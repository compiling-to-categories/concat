{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Domain-typed arrays

module ConCat.TArr where

import GHC.TypeLits (KnownNat)
import GHC.Types (Nat)

import Data.Finite
import Data.Vector.Sized

import ConCat.Misc ((:*),(:+))

class KnownNat (Card a) => HasFin a where
  type Card a :: Nat
  toFin :: a -> Finite (Card a)
  unFin :: Finite (Card a) -> a

-- instance HasFin ()         where -- ...
-- instance HasFin Bool       where -- ...
-- instance HasFin (Finite n) where -- ...

-- instance (HasFin a, HasFin b) => HasFin (a :+ b) where -- ...
-- instance (HasFin a, HasFin b) => HasFin (a :* b) where -- ...

-- Domain-typed "arrays"
newtype Arr a b = Arr (Vector (Card a) b)

(!) :: HasFin a => Arr a b -> (a -> b)
Arr v ! a = v `index` toFin a

arrTrie :: (HasFin a, HasTrie a) => Arr a b -> Trie a b
arrTrie = toTrie . (!)

-- where
class HasTrie a where
  type Trie a :: * -> *
  toTrie :: (a -> b) -> Trie a b
  unTrie :: Trie a b -> (a -> b)

-- instance HasTrie ()         where -- ...
-- instance HasTrie Bool       where -- ...
-- instance HasTrie (Finite n) where -- ...

-- instance (HasTrie a, HasTrie b) => HasTrie (a :+ b) where -- ...
-- instance (HasTrie a, HasTrie b) => HasTrie (a :* b) where -- ...
