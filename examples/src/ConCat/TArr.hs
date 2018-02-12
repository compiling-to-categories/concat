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
-- import Data.Vector.Sized
import qualified Data.Vector.Sized as V

import ConCat.Misc ((:*),(:+))

{----------------------------------------------------------------------
   Some useful isomorphisms.
----------------------------------------------------------------------}

type a :^ b = b -> a

data a <-> b = Iso (a -> b) (b -> a)

type KnownNat2 m n = (KnownNat m, KnownNat n)

finSum :: KnownNat2 m n => Finite (m + n) <-> (Finite m :+ Finite n)
finSum = Iso g h
  where g :: forall m n. KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
        g (Finite l) = if l >= (natValAt @m)
                          then Right $ Finite (l - (natValAt @m))
                          else Left  $ Finite l

        h :: forall m n. KnownNat2 m n => Finite m :+ Finite n -> Finite (m + n)
        h (Left  (Finite l)) = Finite l  -- Need to do it this way, for type conversion.
        h (Right (Finite k)) = Finite (k + (natValAt @m))

finProd :: KnownNat2 m n => Finite (m * n) <-> (Finite m :* Finite n)
finProd = Iso g h
  where g :: forall m n. KnownNat2 m n => Finite (m * n) -> Finite m :* Finite n
        g (Finite l) = let (q,r) = l `divMod` (natValAt @n)
                        in (Finite q, Finite r)

        h :: forall m n. KnownNat2 m n => Finite m :* Finite n -> Finite (m * n)
        h (Finite l, Finite k) = Finite $ l * (natValAt @n) + k

finExp :: KnownNat2 m n => Finite (m ^ n) <-> (Finite m :^ Finite n)
finExp = undefined
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

  -- I really want to write this as:
  --   toFin = h . fmap toFin
  -- but I can't, due to the fact that sums are only functorial in their second type argument.
  -- We can get around this limitation, by wrapping (:+), but only when a ~ b.
  toFin = \case
            (Left  x) -> h $ Left  (toFin x)
            (Right y) -> h $ Right (toFin y)
    where h = isoRev finSum

  unFin n = case (g n) of
              (Left  m) -> Left  (unFin m)
              (Right l) -> Right (unFin l)
    where g = isoFwd finSum

instance (HasFin a, HasFin b, KnownNat (Card a * Card b)) => HasFin (a :* b) where
  type Card (a :* b) = Card a * Card b

  toFin (x,y) = isoRev finProd (toFin x, toFin y)

  unFin n = let (m, l) = isoFwd finProd n
             in (unFin m, unFin l)

instance (HasFin a, HasFin b, KnownNat (Card a ^ Card b)) => HasFin (a :^ b) where
  type Card (a :^ b) = Card a ^ Card b

  toFin f = isoRev finExp (toFin . f . unFin)

  unFin n = let f' = isoFwd finExp n
             in (unFin . f' . toFin)

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

