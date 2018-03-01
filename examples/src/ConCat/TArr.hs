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
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Domain-typed arrays

module ConCat.TArr where

import Prelude hiding (id, (.), const, curry)  -- Coming from ConCat.AltCat.

import GHC.TypeLits
import GHC.Types (Nat)

import Data.Proxy
import Data.Tuple            (swap)
-- import Data.Finite           (getFinite)
import Data.Finite.Internal  (Finite(..))
import qualified Data.Vector.Sized as V

import ConCat.AltCat
import qualified ConCat.Category
import ConCat.Misc           ((:*), (:+), cond)

{----------------------------------------------------------------------
   Some useful isomorphisms.
----------------------------------------------------------------------}

type a :^ b = b -> a

data a <-> b = Iso (a -> b) (b -> a)

instance Category (<->) where
  id = Iso id id
  Iso g g' . Iso f f' = Iso (g . f) (f' . g')

instance MonoidalPCat (<->) where
  Iso f f' *** Iso g g' = Iso (f *** g) (f' *** g')

instance MonoidalSCat (<->) where
  Iso f f' +++ Iso g g' = Iso (f +++ g) (f' +++ g')

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

-- Using Horner's rule and its inverse, as per Conal's suggestion.
finExp :: KnownNat2 m n => (Finite m :^ Finite n) <-> Finite (m ^ n)
finExp = Iso h g
  where g :: forall m n. KnownNat2 m n => Finite (m ^ n) -> Finite m :^ Finite n
        g (Finite l) = \ n -> v `V.index` n
          where v :: V.Vector n (Finite m)
                v = V.unfoldrN (first Finite . swap . flip divMod (natValAt @m)) l

        h :: forall m n. KnownNat2 m n => Finite m :^ Finite n -> Finite (m ^ n)
        -- h f = Finite $ V.foldl' (\accum m -> accum * (natValAt @m) + getFinite m)
        --                       0
        --                       $ V.reverse $ V.generate_ f
        -- h f = V.foldl' (curry u) (Finite 0) ((V.reverse . V.generate_) f)
        -- h = V.foldl' (curry u) (Finite 0) . (V.reverse . V.generate_)
        h = (V.foldl' . curry) u (Finite 0) . (V.reverse . V.generate_)
          where u (Finite acc, Finite m) = Finite $ acc * natValAt @m + m

isoFwd :: a <-> b -> a -> b
isoFwd (Iso g _) = g

isoRev :: a <-> b -> b -> a
isoRev (Iso _ h) = h

toFin :: HasFin a => a -> Finite (Card a)
toFin = isoFwd iso

unFin :: HasFin a => Finite (Card a) -> a
unFin = isoRev iso

inFin :: (HasFin a, HasFin b) => (Finite (Card a) -> Finite (Card b)) -> a -> b
inFin f' = unFin . f' . toFin

liftFin :: (HasFin a, HasFin b) => (a -> b) -> Finite (Card a) -> Finite (Card b)
liftFin f = toFin . f . unFin

{----------------------------------------------------------------------
   A class of types with known finite representations.
----------------------------------------------------------------------}

class KnownNat (Card a) => HasFin a where
  type Card a :: Nat
  iso :: a <-> Finite (Card a)

instance HasFin () where
  type Card () = 1
  iso = Iso (const (Finite 0)) (const ())

instance HasFin Bool where
  type Card Bool = 2
  iso = Iso (Finite . cond 1 0) (\ (Finite n) -> n > 0)

instance KnownNat n => HasFin (Finite n) where
  type Card (Finite n) = n
  iso = id

instance (HasFin a, HasFin b) => HasFin (a :+ b) where
  type Card (a :+ b) = Card a + Card b
  iso = finSum . (iso +++ iso)

instance (HasFin a, HasFin b) => HasFin (a :* b) where
  type Card (a :* b) = Card a * Card b
  iso = finProd . (iso *** iso)

instance (HasFin a, HasFin b) => HasFin (a :^ b) where
  type Card (a :^ b) = Card a ^ Card b
  iso = finExp . Iso liftFin inFin

{----------------------------------------------------------------------
  Domain-typed "arrays"
----------------------------------------------------------------------}

newtype Arr a b = Arr (V.Vector (Card a) b)

instance Functor (Arr a) where
  fmap f (Arr v) = Arr $ fmap f v  -- fmap f . Arr == Arr . fmap f

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

