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
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -Wredundant-constraints #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Another go at safe array wrappers

#include "AbsTy.inc"
AbsTyPragmas

module ConCat.Arr where

import Data.Monoid ((<>),Sum(..))
import Data.Foldable (Foldable(..),toList)
import Data.Traversable (mapAccumL)
import Control.Applicative (liftA2)
import Control.Arrow ((|||),(***))
import GHC.Generics
  (Generic1(..),U1(..),Par1(..),(:*:)(..),(:.:)(..),M1(..),K1(..))
import Data.Tuple (swap)
import Data.Void

import GHC.Exts (inline)        -- experiment

import Control.Newtype (Newtype(..))

import ConCat.Misc ((:*),(:+), (<~), Unop, inNew, inNew2)
import ConCat.Rep
import ConCat.AltCat (Arr,array,arrAt,at,divC,modC)

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

instance Traversable ((->) Void) where
  traverse :: Applicative g => (a -> g b) -> (Void -> a) -> g (Void -> b)
  traverse _ _ = pure absurd

instance Traversable ((->) ()) where
  traverse :: Applicative g => (a -> g b) -> (() -> a) -> g (() -> b)
  traverse f h = pure <$> f (h ())

bool :: w -> w -> (Bool -> w)
bool e t i = if i then t else e

instance Traversable ((->) Bool) where
  traverse :: Applicative g => (w -> g c) -> (Bool -> w) -> g (Bool -> c)
  traverse f h = bool <$> f (h False) <*> f (h True)

instance (Traversable ((->) a), Traversable ((->) b))
      => Traversable ((->) (a :+ b)) where
  traverse :: Applicative g => (w -> g c) -> (a :+ b -> w) -> g (a :+ b -> c)
  traverse f h = (|||) <$> traverse f (h . Left) <*> traverse f (h . Right)

instance (Traversable ((->) a), Traversable ((->) b))
      => Traversable ((->) (a :* b)) where
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

#ifdef VectorSized

#else

instance Newtype (Arr a b) where
  type O (Arr a b) = a -> b
  pack   = array
  unpack = at
  {-# INLINE pack #-}
  {-# INLINE unpack #-}

-- instance Functor (Arr a) where
--   fmap = inNew . fmap
--   {-# INLINE fmap #-}

instance Applicative (Arr a) where
  pure = pack . pure
  (<*>) = inNew2 (<*>)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

liftArr2 :: forall i a b c. (a -> b -> c) -> (Arr i a -> Arr i b -> Arr i c)
liftArr2 = inNew2 . liftA2

instance Foldable ((->) a) => Foldable (Arr a) where
  foldMap f = foldMap f . unpack
  {-# INLINE foldMap #-}
  -- sum = getSum . foldMap Sum
  -- {-# INLINE sum #-}

-- instance Foldable (Arr Bool) where
--   foldMap f = foldMap f . unpack
--   {-# INLINE foldMap #-}

instance {-# overlapping #-} (Foldable (Arr a), Foldable ((->) b))
      => Foldable (Arr (a :* b)) where
  -- foldMap f = foldMap f . Comp1 . array . curry . at
  -- foldMap f = foldMap f . Comp1 . array . fmap array . curry . at
  -- foldMap f = (foldMap.foldMap) f . array . curry . at
  -- foldMap f = foldMap f . Comp1 . array . curry . at
  -- foldMap f = (foldMap.foldMap) f . array . curry . at
  -- foldMap f = fold . fmap f
  -- foldMap f arr = fold (array (fmap (foldMap f) (curry (at arr))))

  -- foldMap f = foldMap (foldMap f) . array . curry . at

  -- Best so far *for bottom-up trees*
  foldMap f = fold . array . fmap (foldMap f) . curry . at

  -- -- Less biased version. Terrible for both top-down and bottom-up.
  -- foldMap f = fold . array . fmap (foldMap f . array) . curry . at

  -- foldMap f = (foldMap . foldMap) f . array . fmap array .  curry . at
  -- foldMap f = foldMap f . Comp1 . array . fmap array .  curry . at

  -- foldMap f = (foldMap . foldMap) f . fmap array .  array . curry . at

  {-# INLINE foldMap #-}
  -- sum = getSum . foldMap Sum
  -- {-# INLINE sum #-}

#if 0
                                         f       :: c -> m
                                         arr     :: Arr (a :* b) c
                                      at arr     :: a :* b -> c
                               curry (at arr)    :: a -> b -> c
             fmap (foldMap f) (curry (at arr))   :: a -> m
      array (fmap (foldMap f) (curry (at arr)))  :: Arr a m
fold (array (fmap (foldMap f) (curry (at arr)))) :: m

at               :: Arr (a :* b) c -> (a :* b -> c)
curry            :: (a :* b -> c)  -> (a -> b -> c)
fmap (foldMap f) :: (a -> b -> c)  -> (a -> m)
array            :: (a -> m)       -> Arr a m
fold             :: Arr a m        -> m

#endif

#if 0
                                         f      :: c -> m
                                         arr    :: Arr (a :* b) c
                                      at arr    :: a :* b -> c
                               curry (at arr)   :: a -> b -> c
                        array (curry (at arr))  :: Arr a (b -> c)
   foldMap (foldMap f) (array (curry (at arr))) :: m
#endif

#if 0
                                      arr     :: Arr (a :* b) c
                                   at arr     :: a :* b -> c
                            curry (at arr)    :: a -> b -> c
                     array (curry (at arr))   :: Arr a (b -> c)
(foldMap.foldMap) f (array (curry (at arr)))  :: Arr a m
#endif


#if 0

foldMap :: Monoid m => (c -> m) -> Arr (a :* b) c -> m
foldMap f = foldMap f . Comp1 . array . curry . arrAt

                                   arr     :: Arr (a :* b) z
                                at arr     :: a :* b -> z
                         curry (at arr)    :: a -> b -> z
                  array (curry (at arr))   :: Arr a (b -> z)
           Comp1 (array (curry (at arr)))  :: (Arr a :.: (->) b) z
foldMap f (Comp1 (array (curry (at arr)))) :: m

at        :: Arr (a :* b) z -> (a :* b -> z)
curry     :: (a :* b -> z) -> (a -> b -> z)
array     :: (a -> b -> z) -> Arr a (b -> z)
Comp1     :: Arr a (b -> z) -> (Arr a :.: (->) b) z
foldMap f :: (Arr a :.: (->) b) z -> m

#endif

#if 0

at         :: Arr (a :* b) z      -> (a :* b -> z)
curry      :: (a :* b -> z)       -> (a -> b -> z)
fmap array :: (a -> b -> z)       -> (a -> Arr b z)
array      :: (a -> Arr b z)      -> Arr a (Arr b z)
Comp1      :: Arr a (Arr b z)     -> (Arr a :.: Arr b) z
foldMap f  :: (Arr a :.: Arr b) z -> m

#endif

-- instance Traversable ((->) a) => Traversable (Arr a) where
--   traverse f = fmap pack . traverse f . unpack
--   {-# INLINE traverse #-}

-- lscan :: (Traversable f, Monoid a) => f a -> f a :* a
-- lscan = swap . mapAccumL (\ acc a -> (acc <> a,acc)) mempty

-- lsums :: (Traversable f, Num a) => f a -> f a :* a
-- lsums = (fmap getSum *** getSum) . lscan . fmap Sum

{--------------------------------------------------------------------
    Function wrappers with memoization
--------------------------------------------------------------------}

infixr 1 :->

newtype a :-> b = FFun { unFFun :: a -> b }
  deriving (Monoid,Functor,Applicative,Monad)

type FFun = (:->)

instance Newtype (a :-> b) where
  type O (a :-> b) = a -> b
  pack = FFun
  unpack = unFFun

instance HasRep (a :-> b) where
  type Rep (a :-> b) = a -> b
  abst = pack
  repr = unpack

memoFun :: Unop (a -> b)
memoFun = at . array

memoFFun :: Unop (a :-> b)
memoFFun = inNew memoFun
-- memoFFun (FFun f) = FFun (at (array f))

AbsTy(a :-> b)

-- instance FFunctor (FFun a) where
--   fmap = inNew . fmap   -- fmap h (FFun f) = FFun (h . f)

-- instance Applicative (FFun a) where
--   pure = pack . pure
--   (<*>) = inNew2 (<*>)

-- deriving instance Foldable ((->) a) => Foldable (FFun a)

instance Foldable ((->) a) => Foldable (FFun a) where
  foldMap f = foldMap f . unpack
  {-# INLINE foldMap #-}
  -- sum = getSum . foldMap Sum
  -- {-# INLINE sum #-}

instance {-# overlapping #-}
         -- (Foldable ((->) a), Foldable ((->) b))
         -- Foldable ((->) (a :* b))
         (Foldable ((:->) a), Foldable ((->) b))
      => Foldable (FFun (a :* b)) where
  -- foldMap f = foldMap f . unFFun
  -- foldMap f = (foldMap . foldMap) f . curry . unFFun

  -- foldMap f = fold . FFun . memoFun . fmap (foldMap f) . curry . unFFun

  -- foldMap f = fold . (FFun . memoFun . fmap (foldMap f) . curry . unFFun)

  foldMap f = fold . prefoldMapFFun f

  -- foldMap f = fold . inline prefoldMapFFun f

  {-# INLINE foldMap #-}

prefoldMapFFun :: forall a b c m. (Foldable ((->) b), Monoid m)
               => (c -> m) -> (a :* b :-> c) -> (a :-> m)
prefoldMapFFun f = FFun . memoFun . fmap (foldMap f) . curry . unFFun
{-# INLINE prefoldMapFFun #-}


#if 0
                                        FFun h     :: a :* b :-> c
                                             h     :: a :* b -> c
                                       curry h     :: a -> b -> c
                     fmap (foldMap f) (curry h)    :: a -> m
              array (fmap (foldMap f) (curry h))   :: Arr a m
          at (array (fmap (foldMap f) (curry h)))  :: a -> m
            memoFun (fmap (foldMap f) (curry h))   :: a -> m
      FFun (memoFun (fmap (foldMap f) (curry h)))  :: a :-> m
fold (FFun (memoFun (fmap (foldMap f) (curry h)))) :: m
#endif

arrFFun :: Arr a b -> FFun a b
arrFFun = pack . unpack

#endif
