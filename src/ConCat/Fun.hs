{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE UndecidableInstances #-}  -- TEMP

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

{-# OPTIONS_GHC -Wno-orphans #-}

-- | 

module ConCat.Fun where

import Data.Monoid ((<>))
import Data.Foldable
import Control.Applicative (liftA2)
import Control.Arrow ((***),(|||))

import ConCat.Misc ((:+),(:*),(<~),Unop,Binop)

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
  fold h = fold (fold . curry h)

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


-- Note that we can avoid orphans by newtype-wrapping function types:

newtype Fun k v = Fun (k -> v) deriving (Functor,Applicative,Monad,Monoid)

-- Give (non-orphan instances) for other classes:

instance Foldable (Fun ()) where
  foldMap f (Fun h) = f (h ())

instance Foldable (Fun Bool) where
  foldMap f (Fun h) = f (h False) <> f (h True)

-- instance (Foldable (Fun a), Foldable (Fun b)) => Foldable (Fun (a :+ b)) where
--   foldMap f (Fun h) = foldMap f (Fun (h . Left)) <> foldMap f (Fun (h . Right))

-- instance (Foldable (Fun a), Foldable (Fun b)) => Foldable (Fun (a :* b)) where
--   foldMap f (Fun h) = (foldMap . foldMap) f (Fun (Fun <$> curry h))

-- Alternatively,

foldMapFun :: (Foldable (Fun a), Monoid m) => (z -> m) -> (a -> z) -> m
foldMapFun f h = foldMap f (Fun h)

instance (Foldable (Fun a), Foldable (Fun b)) => Foldable (Fun (a :+ b)) where
  foldMap f (Fun h) = foldMapFun f (h . Left) <> foldMapFun f (h . Right)

instance (Foldable (Fun a), Foldable (Fun b)) => Foldable (Fun (a :* b)) where
  foldMap f (Fun h) = (foldMapFun . foldMapFun) f (curry h)


-- Type cardinality.
-- If useful, generalize to card :: Num n => n
class HasCard a where card :: Num n => n
                      -- card :: Int

instance HasCard ()   where card = 1

instance HasCard Bool where card = 2

instance (HasCard a, HasCard b) => HasCard (a :+ b) where
  card = card @a + card @b

instance (HasCard a, HasCard b) => HasCard (a :* b) where
  card = card @a * card @b

-- | Convert to and from the ordinal position within a type.
class Ordable a where
  toOrd :: Num n => a -> n
  unOrd :: (Integral n, Show n, Ord n) => n -> a

instance Ordable () where
  toOrd () = 0
  unOrd 0 = ()
  unOrd i = error ("unOrd @(): bad index: " ++ show i)

instance Ordable Bool where
  -- toOrd b = if b then 1 else 0
  toOrd = bool 0 1
  unOrd 0 = False
  unOrd 1 = True
  unOrd i = error ("unOrd @Bool: bad index: " ++ show i)

instance (Ordable a, HasCard a, Ordable b) => Ordable (a :+ b) where
  toOrd (Left  a) = toOrd a
  toOrd (Right b) = card @a + toOrd b
  unOrd i | i < card @a = Left  (unOrd i)
          | otherwise   = Right (unOrd (i - card @a))

instance (Ordable a, HasCard b, Ordable b) => Ordable (a :* b) where
  toOrd (a,b) = toOrd a * card @b + toOrd b
  -- unOrd i = (unOrd ia, unOrd ib) where (ia,ib) = i `divMod` card @b
  -- unOrd ((`divMod` card @b) -> (ia,ib)) = (unOrd ia, unOrd ib)
  unOrd = (unOrd *** unOrd) . (`divMod` card @b)

-- Maybe use `Enum` instead:

instance (Enum a, HasCard a, Enum b) => Enum (a :+ b) where
  -- fromEnum (Left  a) = fromEnum a
  -- fromEnum (Right b) = card @a + fromEnum b
  fromEnum = fromEnum ||| (card @a +) . fromEnum
  toEnum i | i < card @a = Left  (toEnum i)
           | otherwise   = Right (toEnum (i - card @a))

instance (Enum a, HasCard b, Enum b) => Enum (a :* b) where
  fromEnum (a,b) = fromEnum a * card @b + fromEnum b
  -- toEnum i = (toEnum ia, toEnum ib) where (ia,ib) = i `divMod` card @b
  -- toEnum ((`divMod` card @b) -> (ia,ib)) = (toEnum ia, toEnum ib)
  toEnum = (toEnum *** toEnum) . (`divMod` card @b)

-- I like Enum here, despite orphan instances.


newtype Arr a = Arr (Int -> a) deriving (Monoid,Functor,Applicative,Monad)

unFun :: Enum k => Fun k a -> Arr a
unFun (Fun f) = Arr (f . toEnum)

toFun :: Enum k => Arr a -> Fun k a
toFun (Arr h) = Fun (h . fromEnum)

onFun :: Enum k => (Fun k a -> Fun k b) -> (Arr a -> Arr b)
onFun = unFun <~ toFun
-- onFun h = unFun . h . toFun
-- onFun h f = unFun (h (toFun f))

onFun2 :: Enum k => (Fun k a -> Fun k b -> Fun k c) -> (Arr a -> Arr b -> Arr c)
onFun2 = onFun <~ toFun


type R = Double

sqr :: Num a => Unop a
sqr a = a * a

t1 :: forall k a. (Enum k, Num a) => Unop (Arr a)
t1 = onFun @k (fmap sqr)

t2 :: forall k a. (Enum k, Num a) => Binop (Arr a)
t2 = onFun2 @k (liftA2 (+))

t3 :: forall k a. (Foldable (Fun k), Enum k, Num a) => Arr a -> a
t3 = sum . toFun @k


-- Function from k to v, represented as an "array"
newtype TArr k v = TArr (Int -> v) deriving (Monoid,Functor,Applicative,Monad)

unTArr :: Enum k => TArr k v -> (k -> v)
unTArr (TArr h) = h . fromEnum

toTArr :: Enum k => (k -> v) -> TArr k v   -- inverse of unTArr
toTArr h = TArr (h . toEnum)

-- -- Specification: unTarr is a `Foldable` homomorphism.
-- instance (Foldable ((->) k), Enum k) => Foldable (TArr k) where
--   fold = fold . unTArr
--   -- foldMap f = fold . fmap f
--   -- foldMap f = fold . unTArr . fmap f
--   -- foldMap f = fold . fmap f . unTArr
--   foldMap f = foldMap f . unTArr

#if 0
  foldMap f (TArr h)
== fold (fmap f (TArr h))
== fold (TArr (fmap f h))
== fold (TArr (f . h))
#endif

instance Foldable (TArr ()) where
  fold (TArr h) = h 0
  foldMap f (TArr h) = f (h 0)

#if 0
  fold (TArr h)
== fold (unTArr (TArr h))
== fold (h . fromEnum @())
== fold (\ () -> h (fromEnum ()))
== fold (\ () -> h 0)
== (\ () -> h 0) ()
== h 0

  foldMap f (TArr h)
== foldMap f (unTArr (TArr h))
== foldMap f (h . fromEnum @())
== foldMap f (\ () -> h (fromEnum ()))
== foldMap f (\ () -> h 0)
== f ((\ () -> h 0) ())
== f (h 0)
#endif

instance Foldable (TArr Bool) where
  foldMap f (TArr h) = f (h 0) <> f (h 1)

#if 0
  fold (TArr h)
== fold (unTArr (TArr h))
== fold (h . fromEnum @Bool)
== h (fromEnum False) <> h (fromEnum True)
== h 0 <> h 1

  foldMap f (TArr h)
== foldMap f (h . fromEnum @Bool)
== f (h 0) <> f (h 1)

  foldMap f (TArr h)
== fold (TArr (f . h))
== f (h 0) <> f (h 1)
#endif

instance (Foldable (TArr a), HasCard a, Foldable (TArr b))
      => Foldable (TArr (a :+ b)) where
  foldMap f (TArr h) = fold (TArr @(a :+ b) (f . h))
  fold (TArr h) = fold (TArr @a h) <> fold (TArr @b (h . (card @a +)))

#if 0

  fold (TArr @(a :+ b) h)
== fold (unTArr (TArr h))
== fold (h . fromEnum @(a :+ b))
== fold (h . (fromEnum @a ||| (card @a +) . fromEnum @b))
== fold (h . (fromEnum @a ||| (card @a +) . fromEnum @b) . Left ) <>
   fold (h . (fromEnum @a ||| (card @a +) . fromEnum @b) . Right)
== fold (h . fromEnum @a) <> fold (h . (card @a +) . fromEnum @b)
== fold (TArr @a h) <> fold (TArr @b (h . (card @a +)))

#endif

instance (Foldable (TArr a), Foldable (TArr b), HasCard b)
      => Foldable (TArr (a :* b)) where
  foldMap f (TArr h) = fold (TArr @(a :* b) (f . h))
  fold (TArr h) = 
    fold (TArr @a (\ ia -> let n = ia * card @b in
                             fold (TArr @b (\ ib -> h (n + ib)))))


#if 0

  fold (TArr @(a :* b) h)
== fold (unTArr (TArr h))
== fold (h . fromEnum @(a :* b))
== fold (fold . curry (h . (\ (a,b) -> fromEnum a * card @b + fromEnum b)))
== fold (fold . curry (\ (a,b) -> h (fromEnum a * card @b + fromEnum b)))
== fold (fold . \ a b -> h (fromEnum a * card @b + fromEnum b))
== fold (\ a -> let n = fromEnum a * card @b in fold (\ b -> h (n + fromEnum b)))
== fold ((\ ia -> let n = ia * card @b in
             fold ((\ ib -> h (n + ib)) . fromEnum @b) . fromEnum @a)
== fold (unTarr (TArr @a (\ ia -> let n = ia * card @b in
                            fold (unTarr (TArr @b (\ ib -> h (n + ib)))))))
== fold (TArr @a (\ ia -> let n = ia * card @b in
                            fold (TArr @b (\ ib -> h (n + ib)))))

#endif
