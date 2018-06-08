{-# LANGUAGE CPP #-}
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

#include "AbsTy.inc"
AbsTyPragmas

-- | Experiments with statically sized arrays

module ConCat.NatArr where

import Prelude hiding (Enum(..))
import Control.Arrow ((|||))
import Control.Applicative (liftA2)
import Data.Void (Void,absurd)
import Data.Monoid ((<>),Sum(..))
import GHC.TypeLits
import Data.Array (Array,(!))
import qualified Data.Array as Arr
import Data.Proxy (Proxy(..))
import GHC.Generics ((:*:)(..),(:.:)(..))

import Control.Newtype.Generics (Newtype(..))

import ConCat.Misc ((:*),(:+))
import ConCat.AltCat (Arr,array,arrAt,at,natV,divModC)
import ConCat.Rep (HasRep(..))
AbsTyImports

{--------------------------------------------------------------------
    Domain-typed arrays
--------------------------------------------------------------------}

-- Type cardinality.
class (Enum a, KnownNat (Card a)) => HasCard a where
  type Card a :: Nat

instance HasCard Void where type Card Void = 0
instance HasCard ()   where type Card ()   = 1
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

instance HasCard a => Newtype (DArr a b) where
  type O (DArr a b) = Arr (Card a) b
  pack = DArr
  unpack = unDarr
  {-# INLINE pack #-}
  {-# INLINE unpack #-}

instance HasCard a => HasRep (DArr a b) where
  type Rep (DArr a b) = Arr (Card a) b
  abst = pack
  repr = unpack

AbsTy(DArr a b)

deriving instance HasCard a => Functor (DArr a)
-- deriving instance Foldable (DArr a)

instance HasCard i => Applicative (DArr i) where
  pure x = DArr (pure x)
  DArr fs <*> DArr xs = DArr (fs <*> xs)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

atd :: HasCard a => DArr a b -> a -> b
atd (DArr bs) a = arrAt (bs,fromEnum a)
                  -- bs `at` fromEnum a
{-# INLINE atd #-}

darr :: HasCard a => (a -> b) -> DArr a b
darr f = DArr (array (f . toEnum))
{-# INLINE darr #-}

instance Foldable (DArr Void) where
  foldMap _f _h = mempty
  {-# INLINE foldMap #-}

instance Foldable (DArr ()) where
  foldMap f (atd -> h) = f (h ())
  {-# INLINE foldMap #-}
  sum = getSum . foldMap Sum  -- experiment
  {-# INLINE sum #-}

instance Foldable (DArr Bool) where
  foldMap f (atd -> h) = f (h False) <> f (h True)
  {-# INLINE foldMap #-}
  sum = getSum . foldMap Sum  -- experiment
  {-# INLINE sum #-}

splitDSum :: (HasCard a, HasCard b) => DArr (a :+ b) z -> (DArr a :*: DArr b) z
splitDSum (atd -> h) = darr (h . Left) :*: darr (h . Right)
{-# INLINE splitDSum #-}

instance (HasCard a, HasCard b , Foldable (DArr a), Foldable (DArr b))
      => Foldable (DArr (a :+ b)) where
  -- foldMap f (atd -> h) =
  --   foldMap f (darr (h . Left)) <> foldMap f (darr (h . Right))
  foldMap f = foldMap f . splitDSum
  {-# INLINE foldMap #-}
  sum = getSum . foldMap Sum  -- experiment
  {-# INLINE sum #-}

factorDProd :: (HasCard a, HasCard b) => DArr (a :* b) z -> (DArr a :.: DArr b) z
factorDProd = Comp1 . darr . fmap darr . curry . atd
{-# INLINE factorDProd #-}

-- atd       :: DArr (a :* b) z   -> (a :* b -> z)
-- curry     :: (a :* b -> z)     -> (a -> b -> z)
-- fmap darr :: (a -> b -> z)     -> (a -> DArr b z)
-- darr      :: (a -> DArr b z)   -> DArr a (DArr b z)
-- Comp1     :: DArr a (DArr b z) -> (DArr a :.: DArr b) z

instance ( HasCard a, HasCard b, Enum a, Enum b
         , Foldable (DArr a), Foldable (DArr b) )
      => Foldable (DArr (a :* b)) where
  foldMap f = foldMap f . factorDProd
  {-# INLINE foldMap #-}
  sum = getSum . foldMap Sum  -- experiment
  {-# INLINE sum #-}

{--------------------------------------------------------------------
    Enum
--------------------------------------------------------------------}

-- Custom Enum class using *total* definitions of toEnum.

class Enum a where
  fromEnum' :: a -> Int
  toEnum' :: Int -> a

fromEnum :: Enum a => a -> Int
fromEnum = fromEnum'
{-# INLINE [0] fromEnum #-}

toEnum :: Enum a => Int -> a
toEnum = toEnum'
{-# INLINE [0] toEnum #-}

{-# RULES

-- "toEnum . fromEnum" forall a . toEnum (fromEnum a) = a
-- "fromEnum . toEnum" forall n . fromEnum (toEnum n) = n  -- true in our context

 #-}

instance Enum Void where
  fromEnum' = absurd
  toEnum' _ = error "toEnum on void"

instance Enum () where
  fromEnum' () = 0
  toEnum' _ = ()

instance Enum Bool where
  fromEnum' False = 0
  fromEnum' True  = 1
  toEnum' 0       = False
  toEnum' 1       = True
  -- toEnum'         = (> 0)

card :: forall a. HasCard a => Int
card = natV @(Card a)

instance (Enum a, HasCard a, Enum b) => Enum (a :+ b) where
  -- fromEnum (Left  a) = fromEnum a
  -- fromEnum (Right b) = card @a + fromEnum b
  fromEnum' = fromEnum ||| (card @a +) . fromEnum
  toEnum' i | i < na    = Left  (toEnum i)
            | otherwise = Right (toEnum (i - na))
   where
     na = card @a
  {-# INLINE fromEnum' #-}
  {-# INLINE toEnum' #-}

instance (Enum a, HasCard b, Enum b) => Enum (a :* b) where
  fromEnum' (a,b) = fromEnum a * card @b + fromEnum b
  toEnum' i = (toEnum d, toEnum m)
   where
     (d,m) = divModC (i,card @b)
  {-# INLINE fromEnum' #-}
  {-# INLINE toEnum' #-}

-- The categorical divMod avoids method inlining.
