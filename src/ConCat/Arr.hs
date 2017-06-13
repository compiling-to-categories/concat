{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- Needed for HasCard instances
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{-# OPTIONS -Wno-orphans #-}

-- | Experiments with statically sized arrays

module ConCat.Arr where

import Control.Arrow ((|||))
import Control.Applicative (liftA2)
import Data.Void (Void,absurd)
import Data.Monoid ((<>))
import GHC.TypeLits
import Data.Array (Array,array,(!))
import Data.Proxy (Proxy(..))
import GHC.Generics ((:*:)(..),(:.:)(..))

-- import Data.Constraint (Dict(..),(:-)(..),(\\))

import ConCat.Misc ((:*),(:+))

data Arr (n :: Nat) a = KnownNat n => Arr (Array Int a)

-- For ConCat.Category
class ArrayCat k b where
  arr' :: KnownNat n => (Int -> b) `k` Arr n b
  at'  :: KnownNat n => (Arr n b :* Int) `k` b

instance ArrayCat (->) b where
  arr' = arrFun
  at' (Arr bs,i) = bs ! i

natV :: forall n. KnownNat n => Int
natV = fromInteger (natVal (Proxy :: Proxy n)) - 1

arrFun :: forall n a. KnownNat n => (Int -> a) -> Arr n a
arrFun f = Arr (array (0,m) [(i, f i) | i <- [0..m]]) where m = natV @n
{-# INLINE [0] arrFun #-}

-- For ConCat.AltCat
arr :: (ArrayCat k b, KnownNat n) => (Int -> b) `k` Arr n b
arr = arr
{-# INLINE [0] arr #-}

at  :: (ArrayCat k b, KnownNat n) => (Arr n b :* Int) `k` b
at = at'
{-# INLINE [0] at #-}

atc :: KnownNat n => Arr n b -> Int -> b
atc = curry at

instance KnownNat n => Functor (Arr n) where
  fmap f as = arr (f . atc as)
  -- fmap = fmapArr
  -- fmap f (Arr a) = Arr (fmap f a)

-- fmapArr :: KnownNat n => (a -> b) -> Arr n a -> Arr n b
-- fmapArr f as@(Arr _) = arr (f . atc as)
--                      -- Arr (fmap f a)
-- {-# INLINE [0] fmapArr #-}

instance KnownNat n => Applicative (Arr n) where
  pure x = arr (pure x)
  -- (<*>) = liftArr2 ($)
  -- (<*>) = appArr
  fs <*> as = arr (atc fs <*> atc as)

-- appArr :: Arr n (a -> b) -> Arr n a -> Arr n b
-- appArr (Arr fs) (Arr as) = arr ((fs !) <*> (as !))
-- {-# INLINE [0] appArr #-}

-- -- Remove if liftA2 via (<*>)/appArr works out instead.
-- liftArr2 :: (a -> b -> c) -> Arr n a -> Arr n b -> Arr n c
-- liftArr2 f (Arr as) (Arr bs) = arr (liftA2 f (as !) (bs !))
-- {-# INLINE [0] liftArr2 #-}

{-# RULES

"at/arr" forall f i. at (arr f,i) = f i

-- Maybe at/arr is all I need.

-- "fmap arr" forall f as. fmapArr f (arr as) = arr (fmap f as)

-- "appArr arr" forall fs as. appArr (arr fs) (arr as) = arr (fs <*> as)

-- "liftArr2 arr" forall f as bs. liftArr2 f (arr as) (arr bs) = arr (liftA2 f as bs)

  #-}

-- instance Foldable (Arr n) where foldMap f (Arr a) = foldMap f a

-- -- Maybe drop this instance
-- instance KnownNat n => Foldable (Arr n) where
--   foldMap f a = foldMap f (atc a <$> [0 .. natV @n - 1])

{--------------------------------------------------------------------
    Domain-typed arrays
--------------------------------------------------------------------}

-- -- Type cardinality.
-- -- If useful, generalize to card :: Num n => n
-- class Card a where card :: Nat

-- instance (KnownNat a, KnownNat b) => KnownNat (a :* b) where
  
class (Enum a, KnownNat (Card a)) => HasCard a where
  type Card a :: Nat

instance HasCard () where type Card () = 1

instance HasCard Bool where type Card Bool = 2

instance (HasCard a, HasCard b) => HasCard (a :+ b) where
  type Card (a :+ b) = Card a + Card b

-- • Illegal nested type family application ‘Card a + Card b’
--   (Use UndecidableInstances to permit this)

instance (HasCard a, HasCard b) => HasCard (a :* b) where
  type Card (a :* b) = Card a * Card b

-- Without GHC.TypeLits.KnownNat.Solver (from ghc-typelits-knownnat):
-- 
--   • Could not deduce (KnownNat (Card a + Card b))
--       arising from the superclasses of an instance declaration
--     from the context: (HasCard a, HasCard b)
--   
--   • Could not deduce (KnownNat (Card a * Card b))
--       arising from the superclasses of an instance declaration
--     from the context: (HasCard a, HasCard b)

data DArr a b = DArr { unDarr :: Arr (Card a) b }

deriving instance HasCard a => Functor (DArr a)
-- deriving instance Foldable (DArr a)

instance HasCard i => Applicative (DArr i) where
  pure x = DArr (pure x)
  DArr fs <*> DArr xs = DArr (fs <*> xs)

atd :: HasCard a => DArr a b -> a -> b
atd (DArr bs) a = atc bs (fromEnum a)

darr :: HasCard a => (a -> b) -> DArr a b
darr f = DArr (arr (f . toEnum))

instance Foldable (DArr Void) where
  foldMap _f _h = mempty

instance Foldable (DArr ()) where
  foldMap f (atd -> h) = f (h ())

instance Foldable (DArr Bool) where
  foldMap f (atd -> h) = f (h False) <> f (h True)

splitDSum :: (HasCard a, HasCard b) => DArr (a :+ b) z -> (DArr a :*: DArr b) z
splitDSum (atd -> h) = darr (h . Left) :*: darr (h . Right)

instance (HasCard a, HasCard b , Foldable (DArr a), Foldable (DArr b))
      => Foldable (DArr (a :+ b)) where
  -- foldMap f (atd -> h) =
  --   foldMap f (darr (h . Left)) <> foldMap f (darr (h . Right))
  foldMap f = foldMap f . splitDSum

factorDProd :: (HasCard a, HasCard b) => DArr (a :* b) z -> (DArr a :.: DArr b) z
factorDProd = Comp1 . darr . fmap darr . curry . atd

-- atd       :: DArr (a :* b) z   -> (a :* b -> z)
-- curry     :: (a :* b -> z)     -> (a -> b -> z)
-- fmap darr :: (a -> b -> z)     -> (a -> DArr b z)
-- darr      :: (a -> DArr b z)   -> DArr a (DArr b z)
-- Comp1     :: DArr a (DArr b z) -> (DArr a :.: DArr b) z

instance ( HasCard a, HasCard b, Enum a, Enum b
         , Foldable (DArr a), Foldable (DArr b) )
      => Foldable (DArr (a :* b)) where
  foldMap f = foldMap f . factorDProd

{--------------------------------------------------------------------
    Missing Enum instances
--------------------------------------------------------------------}
instance Enum Void where
  fromEnum = absurd
  toEnum _ = error "toEnum on void"

card :: forall a. HasCard a => Int
card = natV @(Card a)

instance (Enum a, HasCard a, Enum b) => Enum (a :+ b) where
  -- fromEnum (Left  a) = fromEnum a
  -- fromEnum (Right b) = card @a + fromEnum b
  fromEnum = fromEnum ||| (natV @(Card a) +) . fromEnum
  toEnum i | i < na    = Left  (toEnum i)
           | otherwise = Right (toEnum (i - na))
   where
     na = natV @(Card a)
  {-# INLINE fromEnum #-}
  {-# INLINE toEnum #-}

instance (Enum a, HasCard b, Enum b) => Enum (a :* b) where
  fromEnum (a,b) = fromEnum a * natV @(Card b) + fromEnum b
  toEnum i = (toEnum d, toEnum m)
   where
     (d,m) = i `divMod` n
     n = card @b
  {-# INLINE fromEnum #-}
  {-# INLINE toEnum #-}

-- Switch to categorical divMod to avoid method inlining.
