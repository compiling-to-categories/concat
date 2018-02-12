{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Domain-typed arrays

module ConCat.TArr where

import GHC.TypeLits
import GHC.Types (Nat)

import Data.Proxy
import Data.Finite
import Data.Finite.Internal (Finite(..))
import Data.Vector.Sized
import qualified Data.Vector.Sized as V

import ConCat.Misc ((:*),(:+))

{----------------------------------------------------------------------
   Some useful isomorphisms.
----------------------------------------------------------------------}

type a :^ b = b -> a

data a <-> b = Iso (a -> b) (b -> a)

type KnownNat2 m n = (KnownNat m, KnownNat n)

finSum  :: KnownNat2 m n => Finite (m + n) <-> (Finite m :+ Finite n)
finSum  = undefined

finProd :: KnownNat2 m n => Finite (m * n) <-> Finite m :* Finite n
finProd = undefined

finExp  :: KnownNat2 m n => Finite (m ^ n) <-> Finite m :^ Finite n
finExp  = undefined

{----------------------------------------------------------------------
   A class of types with known finite representations.
----------------------------------------------------------------------}

class KnownNat (Card a) => HasFin a where
  type Card a :: Nat
  toFin :: a -> Finite (Card a)
  unFin :: Finite (Card a) -> a

instance HasFin () where
  type Card () = 1
  toFin _ = Finite 0
  unFin _ = ()

instance HasFin Bool where
  type Card Bool = 2

  toFin False = Finite 0
  toFin True  = Finite 1

  unFin (Finite 0) = False
  unFin _          = True

instance KnownNat n => HasFin (Finite n) where
  type Card (Finite n) = n
  toFin = id
  unFin = id

instance (HasFin a, HasFin b, KnownNat (Card a + Card b)) => HasFin (a :+ b) where
  type Card (a :+ b) = Card a + Card b

  toFin = let (Iso _ h) = finSum
           in \case
                (Left  x) -> h $ Left  (toFin x)
                (Right y) -> h $ Right (toFin y)

  unFin n = let (Iso g _) = finSum
             in case (g n) of
                (Left  m) -> Left  (unFin m)
                (Right l) -> Right (unFin l)

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

{----------------------------------------------------------------------
  Utilities
----------------------------------------------------------------------}

natValAt :: forall n. KnownNat n => Integer
natValAt = natVal (Proxy @n)

