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
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Domain-typed arrays

module ConCat.TArr where

import Prelude hiding (id, (.))  -- Coming from Control.Category.

import GHC.TypeLits
import GHC.Types (Nat)

import Control.Arrow        (first, second)
import qualified Control.Arrow as A
import Control.Category
import Data.Proxy
import Data.Finite
import Data.Finite.Internal (Finite(..))
import qualified Data.Vector.Sized as V

-- import ConCat.AltCat
-- import ConCat.Category ((+++),(***))
import ConCat.Misc     ((:*), (:+), cond)

{----------------------------------------------------------------------
   Some useful isomorphisms.
----------------------------------------------------------------------}

type a :^ b = b -> a

data a <-> b = Iso (a -> b) (b -> a)

instance Category (<->) where
  id = Iso id id
  (Iso g h) . (Iso g' h') = Iso (g . g') (h' . h)

infixr 3 ***
infixr 2 +++

(***) :: (a <-> c) -> (b <-> d) -> ((a :* b) <-> (c :* d))
Iso g h *** Iso g' h' = Iso (g A.*** g') (h A.*** h')

(+++) :: (a <-> c) -> (b <-> d) -> ((a :+ b) <-> (c :+ d))
Iso g h +++ Iso g' h' = Iso (g A.+++ g') (h A.+++ h')

type KnownNat2 m n = (KnownNat m, KnownNat n)

finSum :: KnownNat2 m n => (Finite m :+ Finite n) <-> Finite (m + n)
finSum = Iso h g
  where g :: forall m n. KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
        g (Finite l) = if l >= natValAt @m
                          then Right $ Finite (l - natValAt @m)
                          else Left  $ Finite l

        h :: forall m n. KnownNat2 m n => Finite m :+ Finite n -> Finite (m + n)
        h (Left  (Finite l)) = Finite l  -- Need to do it this way, for type conversion.
        h (Right (Finite k)) = Finite (k + natValAt @m)

finProd :: KnownNat2 m n => (Finite m :* Finite n) <-> Finite (m * n)
finProd = Iso h g
  where g :: forall m n. KnownNat2 m n => Finite (m * n) -> Finite m :* Finite n
        g (Finite l) = let (q,r) = l `divMod` natValAt @n
                        in (Finite q, Finite r)

        h :: forall m n. KnownNat2 m n => Finite m :* Finite n -> Finite (m * n)
        h (Finite l, Finite k) = Finite $ l * natValAt @n + k

-- finExp :: KnownNat2 m n => Finite (m ^ n) <-> (Finite m :^ Finite n)
-- finExp = undefined
-- finExp = Iso g h
--   where g :: forall m n. KnownNat2 m n => Finite (m ^ n) -> Finite m :^ Finite n
--         -- g (Finite l) =  -- Unique, n-element factorization? What about ordering?
--         g = undefined

--         h :: forall m n. KnownNat2 m n => Finite m :^ Finite n -> Finite (m ^ n)
--         h f = Finite $ product [(inFin f) l | l <- [0..((natValAt @n)-1)]]

--         inFin :: (Finite n -> Finite m) -> Integer -> Integer
--         inFin f' = unFin . f' . toFin

isoFwd :: a <-> b -> a -> b
isoFwd (Iso g _) = g

isoRev :: a <-> b -> b -> a
isoRev (Iso _ h) = h

{----------------------------------------------------------------------
   A class of types with known finite representations.
----------------------------------------------------------------------}

class KnownNat (Card a) => HasFin a where
  type Card a :: Nat

  iso :: a <-> Finite (Card a)
  iso = Iso toFin unFin

  toFin :: a -> Finite (Card a)
  toFin = isoFwd iso

  unFin :: Finite (Card a) -> a
  unFin = isoRev iso

  {-# MINIMAL (iso | (toFin, unFin)) #-}

instance HasFin () where
  type Card () = 1
  iso = Iso (const (Finite 0)) (const ())

instance HasFin Bool where
  type Card Bool = 2

  toFin = Finite . cond 1 0

  unFin (Finite n) = n > 0

instance KnownNat n => HasFin (Finite n) where
  type Card (Finite n) = n

  iso = id

instance (HasFin a, HasFin b) => HasFin (a :+ b) where
  type Card (a :+ b) = Card a + Card b

  iso = finSum . (iso +++ iso)

instance (HasFin a, HasFin b) => HasFin (a :* b) where
  type Card (a :* b) = Card a * Card b

  iso = finProd . (iso *** iso)

-- Domain-typed "arrays"
newtype Arr a b = Arr (V.Vector (Card a) b)

instance Functor (Arr a) where
  fmap f (Arr v) = Arr $ V.map f v

(!) :: HasFin a => Arr a b -> (a -> b)
Arr v ! a = v `V.index` toFin a

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

