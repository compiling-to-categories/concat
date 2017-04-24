{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -Wredundant-constraints #-}
{-# OPTIONS_GHC -Wno-orphans #-}

#include "AbsTy.inc"
AbsTyPragmas

#define CustomEnum

-- | Another go at safe array wrappers

module ConCat.Fun where

#ifdef CustomEnum
import Prelude hiding (Enum(..))
#endif

import Control.Arrow ((|||),(***))
import GHC.Generics
  (Generic1(..),U1(..),Par1(..),(:*:)(..),(:.:)(..),M1(..),K1(..))
import Data.Tuple (swap)
import Data.Void
import Data.Monoid ((<>),Sum(..))
import Data.Foldable (Foldable(..),toList)
import Data.Traversable (mapAccumL)

import Control.Newtype

import ConCat.Misc ((:*),(:+), (<~), inNew, inNew2)
import ConCat.Rep
import ConCat.AltCat (Arr,mkArr,arrAt,divC,modC)

AbsTyImports

{--------------------------------------------------------------------
    Foldable functions
--------------------------------------------------------------------}

instance Foldable ((->) Void) where
  foldMap _f _h = mempty

instance Foldable ((->) ()) where
  foldMap f h = f (h ())

#if 0

   h     :: () -> c
f        :: c -> m
f (h ()) :: m

#endif

instance Foldable ((->) Bool) where
  foldMap f h = f (h False) <> f (h True)
  fold h = h False <> h True

#if 0

   h        :: Bool -> c
f           :: c -> m
f (h False) :: m
f (h True ) :: m

#endif

instance (Foldable ((->) a), Foldable ((->) b)) => Foldable ((->) (a :+ b)) where
  foldMap f h = foldMap f (h . Left) <> foldMap f (h . Right)
  fold h = fold (h . Left) <> fold (h . Right)

#if 0

           h          :: a :+ b -> c
           h . Left   :: a -> c
           h . Right  :: b -> c
        f             :: c -> m
foldMap f (h . Left ) :: m
foldMap f (h . Right) :: m

#endif

instance (Foldable ((->) a), Foldable ((->) b)) => Foldable ((->) (a :* b)) where
  foldMap f h = (foldMap . foldMap) f (curry h)
  -- fold h = fold (fmap fold (curry h))
  fold = fold . fmap fold . curry
  -- fold h = fold (fold . curry h)

#if 0

                           h  :: a :* b -> c
                     curry h  :: a -> b -> c
                 f            :: c -> m
         foldMap f            :: (b -> c) -> m
foldMap (foldMap f)           :: (a -> b -> c) -> m
foldMap (foldMap f) (curry h) :: m

#endif


instance Traversable ((->) ()) where
  traverse :: Applicative g => (a -> g b) -> (() -> a) -> g (() -> b)
  traverse f h = pure <$> f (h ())

#if 0
data Pair a = a :# a

instance Functor Pair where fmap f (a :# b) = f a :# f b

instance Foldable Pair where foldMap f (a :# b) = f a <> f b

instance Traversable Pair where traverse f (a :# b) = (:#) <$> f a <*> f b
#endif

bool :: w -> w -> (Bool -> w)
bool e t i = if i then t else e

instance Traversable ((->) Bool) where
  traverse :: Applicative g => (w -> g c) -> (Bool -> w) -> g (Bool -> c)
  traverse f h = bool <$> f (h False) <*> f (h True)

instance (Traversable ((->) a), Traversable ((->) b)) => Traversable ((->) (a :+ b)) where
  traverse :: Applicative g => (w -> g c) -> (a :+ b -> w) -> g (a :+ b -> c)
  traverse f h = (|||) <$> traverse f (h . Left) <*> traverse f (h . Right)

instance (Traversable ((->) a), Traversable ((->) b)) => Traversable ((->) (a :* b)) where
  traverse :: Applicative g => (w -> g c) -> (a :* b -> w) -> g (a :* b -> c)
  traverse f h = uncurry <$> (traverse.traverse) f (curry h)

#if 0
            
                                         h  :: a :* b -> w
                                   curry h  :: a -> b -> w
                               f            :: w -> g c
                      traverse f            :: (b -> w) -> g (b -> c)
            traverse (traverse f)           :: (a -> b -> w) -> g (a -> b -> c)
            traverse (traverse f) (curry h) :: g (a -> b -> c)
uncurry <$> traverse (traverse f) (curry h) :: g (a :* b -> c)

#endif

instance Newtype (Arr a b) where
  type O (Arr a b) = a -> b
  pack   = mkArr
  unpack = curry arrAt
  {-# INLINE pack #-}
  {-# INLINE unpack #-}

instance Functor (Arr a) where
  fmap = inNew . fmap
  {-# INLINE fmap #-}

instance Applicative (Arr a) where
  pure = pack . pure
  (<*>) = inNew2 (<*>)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

instance Foldable ((->) a) => Foldable (Arr a) where
  foldMap f = foldMap f . unpack
  {-# INLINE foldMap #-}

instance {-# overlapping #-} (Foldable (Arr a), Foldable ((->) b))
      => Foldable (Arr (a :* b)) where
  foldMap f arr = fold (mkArr (fmap (foldMap f) (curry (curry arrAt arr))))
  {-# INLINE foldMap #-}

-- f :: c -> m
-- arr :: Arr (a :* b) c
-- curry arrAt arr :: a :* b -> c
-- curry (curry arrAt arr) :: a -> b -> c
-- fmap (foldMap f) (curry (curry arrAt arr)) :: a -> m
-- mkArr (fmap (foldMap f) (curry (curry arrAt arr))) :: Arr a m
-- fold (mkArr (fmap (foldMap f) (curry (curry arrAt arr)))) :: m



instance Traversable ((->) a) => Traversable (Arr a) where
  traverse f = fmap pack . traverse f . unpack
  {-# INLINE traverse #-}

lscan :: (Traversable f, Monoid a) => f a -> f a :* a
lscan = swap . mapAccumL (\ acc a -> (acc <> a,acc)) mempty

lsums :: (Traversable f, Num a) => f a -> f a :* a
lsums = (fmap getSum *** getSum) . lscan . fmap Sum
