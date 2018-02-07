{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Domain-typed arrays

module ConCat.TArr where

-- import GHC.TypeLits (KnownNat)
import GHC.TypeLits
import GHC.Types (Nat)

import Data.Proxy
import Data.Finite
import Data.Vector.Sized
import qualified Data.Vector.Sized as V

import ConCat.Misc ((:*),(:+))

class KnownNat (Card a) => HasFin a where
  type Card a :: Nat
  toFin :: a -> Finite (Card a)
  unFin :: Finite (Card a) -> a

instance HasFin () where
  type Card () = 1
  toFin _ = finite 0
  unFin _ = ()

instance HasFin Bool where
  type Card Bool = 2

  toFin False = finite 0
  toFin True  = finite 1

  unFin x = case (getFinite x) of
              0 -> False
              1 -> True
              _ -> error "Yikes! We just got a numerical representation of Bool >1."

instance KnownNat n => HasFin (Finite n) where
  type Card (Finite n) = n
  toFin = id
  unFin = id

instance (HasFin a, HasFin b, KnownNat (Card a + Card b)) => HasFin (a :+ b) where
  type Card (a :+ b) = Card a + Card b

  toFin (Left  x) = (finite . getFinite . toFin) x
  toFin (Right y) = finite $ natVal (Proxy @(Card a)) + (getFinite . toFin) y

  unFin n = if getFinite n < natVal (Proxy @(Card a))
               then Left  ((unFin . finite . getFinite) n)
               else Right ((unFin . finite) $ getFinite n - natVal (Proxy @(Card a)))

instance (HasFin a, HasFin b, KnownNat (Card a * Card b)) => HasFin (a :* b) where
  type Card (a :* b) = Card a * Card b

  toFin (x,y) = finite $ (getFinite . toFin) x * (natVal (Proxy @(Card b))) + (getFinite . toFin) y

  unFin n = let (q,r) = (getFinite . toFin) n `divMod` (natVal (Proxy @(Card b)))
             in ((unFin . finite) q, (unFin . finite) r)

-- Domain-typed "arrays"
newtype Arr a b = Arr (Vector (Card a) b)

instance Functor (Arr a) where
  fmap f (Arr v) = Arr $ V.map f v

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
