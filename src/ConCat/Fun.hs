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

#include "AbsTy.inc"
AbsTyPragmas

-- #define CustomEnum

-- | Another go at safe array wrappers

module ConCat.Fun where

#ifdef CustomEnum
import Prelude hiding (Enum(..))
#endif

import Data.Monoid ((<>),Sum(..))
import Data.Foldable (Foldable(..),toList)
import Data.Traversable (mapAccumL)
import Control.Applicative (liftA2)
import Control.Arrow ((|||),(***))
import GHC.Generics
  (Generic1(..),U1(..),Par1(..),(:*:)(..),(:.:)(..),M1(..),K1(..))
import Data.Tuple (swap)
import Data.Void

import Control.Newtype (Newtype(..))

import ConCat.Misc ((:*),(:+), (<~), inNew, inNew2)
import ConCat.Rep
import ConCat.AltCat (Arr,array,arrAt,divC,modC)

AbsTyImports

{--------------------------------------------------------------------
    Some missing Enum instances
--------------------------------------------------------------------}

#ifdef CustomEnum
-- Define a new class instead of instantiating the usual one. I want total toEnum.

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

"toEnum . fromEnum" forall a . toEnum (fromEnum a) = a
"fromEnum . toEnum" forall n . fromEnum (toEnum n) = n  -- true in our context

 #-}

instance Enum () where
  fromEnum () = 0
  toEnum _ = ()

instance Enum Bool where
  fromEnum False = 0
  fromEnum True  = 1
  toEnum 0 = False
  toEnum 1 = True
--   toEnum = (> 0)

#endif

instance Enum Void where
  fromEnum = absurd
  toEnum _ = error "toEnum on void"

instance (Enum a, Card a, Enum b) => Enum (a :+ b) where
  -- fromEnum (Left  a) = fromEnum a
  -- fromEnum (Right b) = card @a + fromEnum b
  fromEnum = fromEnum ||| (card @a +) . fromEnum
  toEnum i | i < card @a = Left  (toEnum i)
            | otherwise   = Right (toEnum (i - card @a))
  {-# INLINE fromEnum #-}
  {-# INLINE toEnum #-}

instance (Enum a, Card b, Enum b) => Enum (a :* b) where
  fromEnum (a,b) = fromEnum a * card @b + fromEnum b
  -- toEnum i = (toEnum ia, toEnum ib) where (ia,ib) = i `divMod` card @b
  -- toEnum ((`divMod` card @b) -> (ia,ib)) = (toEnum ia, toEnum ib)
  -- toEnum = (toEnum *** toEnum) . (`divMod` card @b) -- reboxing trouble
  -- toEnum i = (toEnum (i `div` n), toEnum (i `mod` n)) where n = card @b
  toEnum i = (toEnum (divC (i,n)), toEnum (modC (i,n))) where n = card @b
  {-# INLINE fromEnum #-}
  {-# INLINE toEnum #-}

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

#if 1

-- Type cardinality.
-- If useful, generalize to card :: Num n => n
class Card a where card :: Int

instance Card Void where card = 0

instance Card ()   where card = 1

instance Card Bool where card = 2

instance (Card a, Card b) => Card (a :+ b) where
  card = card @a + card @b

instance (Card a, Card b) => Card (a :* b) where
  card = card @a * card @b

instance (Card a, Card b) => Card (a -> b) where
  card = card @b ^ card @a

data Arr' a b = (Enum a, Card a) => Arr' (Arr b)

instance (Enum a, Card a) => Newtype (Arr' a b) where
  type O (Arr' a b) = Arr b
  pack arr = Arr' arr
  unpack (Arr' arr) = arr
  {-# INLINE pack #-}
  {-# INLINE unpack #-}

instance (Enum a, Card a) => HasRep (Arr' a b) where
  type Rep (Arr' a b) = O (Arr' a b)
  abst = pack
  repr = unpack

type ArrQ = Arr'  -- CPP hack
AbsTy(ArrQ a b)

arr' :: forall a b. (Enum a, Card a) => (Int -> b) -> Arr' a b
arr' f = Arr' (array (card @a, f))

arrAt' :: Arr' a b -> (Int -> b)
arrAt' (Arr' arr) = curry arrAt arr

inArr' :: (Enum b, Card b)
       => ((Int -> p) -> (Int -> q)) -> (Arr' a p -> Arr' b q)
inArr' = arr' <~ arrAt'

inArr2' :: (Enum c, Card c)
        => ((Int -> p) -> (Int -> q) -> (Int -> r)) -> (Arr' a p -> Arr' b q -> Arr' c r)
inArr2' = inArr' <~ arrAt'

instance (Enum a, Card a) => Functor (Arr' a) where
  fmap = inArr' . fmap
  {-# INLINE fmap #-}

instance (Enum a, Card a) => Applicative (Arr' a) where
  pure = arr' . pure
  -- (<*>) = inArr2' (<*>)
  (<*>) = liftArr2 ($)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

liftArr2 :: (Enum a, Card a) => (p -> q -> r) -> Arr' a p -> Arr' a q -> Arr' a r
liftArr2 = inArr2' . liftA2
-- liftArr2 op p q = arr' (\ i -> arrAt' p i `op` arrAt' q i)

instance Foldable (Arr' ()) where
  foldMap f (arrAt' -> h) = f (h 0)
  {-# INLINE foldMap #-}

instance Foldable (Arr' Bool) where
  foldMap f (arrAt' -> h) = f (h 0) <> f (h 1)
  {-# INLINE foldMap #-}

instance {-# overlapping #-} ( Enum a, Card a, Enum b, Card b
                             , Foldable (Arr' a), Foldable ((->) b) )
      => Foldable (Arr' (a :* b)) where
  -- foldMap f arr = (foldMap.foldMap) f (array (fmap array (curry (curry arrAt arr . comb))))
  -- foldMap f (arrAt' -> h) = fold (array (fmap (foldMap f . array) (curry (h . comb))))
  foldMap f (arrAt' -> h) =
  --   (foldMap.foldMap) f (arr' @a (fmap (arr' @b) (curry (h . comb))))
  --   fold (arr' @a (fmap (foldMap f . arr' @b) (curry (h . comb))))
    fold (arr' @a (fmap (foldMap f . (. fromEnum @b)) (curry (h . comb))))
   where
     comb (j,k) = card @b * j + k
  {-# INLINE foldMap #-}

#if 0
                                                          h            :: Int -> c
                                                          h . comb     :: Int * Int -> c
                                                   curry (h . comb)    :: Int -> Int -> c
               fmap (            (. fromEnum @b)) (curry (h . comb))   :: Int -> b -> c
               fmap (foldMap f . (. fromEnum @b)) (curry (h . comb))   :: Int -> m
      arr' @a (fmap (foldMap f . (. fromEnum @b)) (curry (h . comb)))  :: Arr' a m
fold (arr' @a (fmap (foldMap f . (. fromEnum @b)) (curry (h . comb)))) :: m
#endif

#if 0
                                            h                  :: Int -> c
                                            h . comb           :: Int :* Int -> c
                                     curry (h . comb)          :: Int -> Int -> c
               fmap (            arr' @b) (curry (h . comb))   :: Int -> Arr' c
               fmap (foldMap f . arr' @b) (curry (h . comb))   :: Int -> m
      arr' @a (fmap (foldMap f . arr' @b) (curry (h . comb)))  :: Arr' a m
fold (arr' @a (fmap (foldMap f . arr' @b) (curry (h . comb)))) :: m
#endif

#if 0
                                                     h            :: Int -> c
                                                     h . comb     :: Int :* Int -> c
                                              curry (h . comb)    :: Int -> Int -> c
                              fmap (arr' @b) (curry (h . comb))   :: Int -> Arr' b c
                     arr' @a (fmap (arr' @b) (curry (h . comb)))  :: Arr' a (Arr' b c)
(foldMap.foldMap) f (arr' @a (fmap (arr' @b) (curry (h . comb)))) :: m
#endif


#if 0

foldMap :: Monoid m => (c -> m) -> Arr (a :* b) c -> m
foldMap f = foldMap f . Comp1 . array . curry . arrAt

                                      arr     :: Arr (a :* b) z
                                arrAt arr     :: a :* b -> z
                         curry (arrAt arr)    :: a -> b -> z
                  array (curry (arrAt arr))   :: Arr a (b -> z)
           Comp1 (array (curry (arrAt arr)))  :: (Arr a :.: (->) b) z
foldMap f (Comp1 (array (curry (arrAt arr)))) :: m

arrAt     :: Arr (a :* b) z -> (a :* b -> z)
curry     :: (a :* b -> z) -> (a -> b -> z)
array     :: (a -> b -> z) -> Arr a (b -> z)
Comp1     :: Arr a (b -> z) -> (Arr a :.: (->) b) z
foldMap f :: (Arr a :.: (->) b) z -> m

#endif

#else

instance Newtype (Arr a b) where
  type O (Arr a b) = a -> b
  pack   = array
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
  -- sum = getSum . foldMap Sum
  -- {-# INLINE sum #-}

-- instance Foldable (Arr Bool) where
--   foldMap f = foldMap f . unpack
--   {-# INLINE foldMap #-}

instance {-# overlapping #-} (Foldable (Arr a), Foldable ((->) b))
      => Foldable (Arr (a :* b)) where
#if 0
  -- foldMap f = foldMap f . Comp1 . array . curry . curry arrAt
  -- foldMap f = (foldMap.foldMap) f . array . curry . curry arrAt
  -- foldMap f = foldMap f . Comp1 . array . curry . curry arrAt
  -- foldMap f = (foldMap.foldMap) f . array . curry . curry arrAt
  -- foldMap f = fold . fmap f
#else
  -- foldMap f arr = fold (array (fmap (foldMap f) (curry (curry arrAt arr))))
  foldMap f = fold . array . fmap (foldMap f) . curry . curry arrAt
  -- foldMap f = fold . array . fmap (foldMap f . array) . curry . curry arrAt
#endif
  {-# INLINE foldMap #-}
  -- sum = getSum . foldMap Sum
  -- {-# INLINE sum #-}

#if 0
                                                  f       :: c -> m
                                                  arr     :: Arr (a :* b) c
                                      curry arrAt arr     :: a :* b -> c
                               curry (curry arrAt arr)    :: a -> b -> c
             fmap (foldMap f) (curry (curry arrAt arr))   :: a -> m
      array (fmap (foldMap f) (curry (curry arrAt arr)))  :: Arr a m
fold (array (fmap (foldMap f) (curry (curry arrAt arr)))) :: m
#endif

#if 0
                                               arr     :: Arr (a :* b) c
                                   curry arrAt arr     :: a :* b -> c
                            curry (curry arrAt arr)    :: a -> b -> c
                     array (curry (curry arrAt arr))   :: Arr a (b -> c)
(foldMap.foldMap) f (array (curry (curry arrAt arr)))  :: Arr a m
#endif


#if 0

foldMap :: Monoid m => (c -> m) -> Arr (a :* b) c -> m
foldMap f = foldMap f . Comp1 . array . curry . arrAt

                                      arr     :: Arr (a :* b) z
                                arrAt arr     :: a :* b -> z
                         curry (arrAt arr)    :: a -> b -> z
                  array (curry (arrAt arr))   :: Arr a (b -> z)
           Comp1 (array (curry (arrAt arr)))  :: (Arr a :.: (->) b) z
foldMap f (Comp1 (array (curry (arrAt arr)))) :: m

arrAt     :: Arr (a :* b) z -> (a :* b -> z)
curry     :: (a :* b -> z) -> (a -> b -> z)
array     :: (a -> b -> z) -> Arr a (b -> z)
Comp1     :: Arr a (b -> z) -> (Arr a :.: (->) b) z
foldMap f :: (Arr a :.: (->) b) z -> m

#endif

#endif

-- instance Traversable ((->) a) => Traversable (Arr a) where
--   traverse f = fmap pack . traverse f . unpack
--   {-# INLINE traverse #-}

-- lscan :: (Traversable f, Monoid a) => f a -> f a :* a
-- lscan = swap . mapAccumL (\ acc a -> (acc <> a,acc)) mempty

-- lsums :: (Traversable f, Num a) => f a -> f a :* a
-- lsums = (fmap getSum *** getSum) . lscan . fmap Sum
