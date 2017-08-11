{-# LANGUAGE CPP                 #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Sized
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Statically sized functors
----------------------------------------------------------------------

-- TODO: Reconsider whether I can use 'length' from 'Foldable' rather than the
-- Sized type class. Can 'Foldable.length' operate efficiently on our data types
-- (without traversing)?

module ConCat.Sized (Sized(..),genericSize) where

-- TODO: explicit exports

import GHC.Generics

class Sized (f :: * -> *) where
  size :: Int
  -- dummySized :: ()
  -- dummySized = ()

-- TODO: Switch from f () to f Void or Proxy

-- | Generic 'size'
genericSize :: forall f. Sized (Rep1 f) => Int
genericSize = size @(Rep1 f)
{-# INLINABLE genericSize #-}

-- -- | Default for 'size' on an applicative foldable.
-- -- Warning: runs in linear time (though possibly at compile time).
-- sizeAF :: forall f. (Applicative f, Foldable f) => Int
-- sizeAF = sum (pure 1 :: f Int)

{--------------------------------------------------------------------
    Generics
--------------------------------------------------------------------}

instance Sized U1 where
  size = 0
  {-# INLINABLE size #-}

instance Sized Par1 where
  size = 1
  {-# INLINABLE size #-}

instance Sized (K1 i c) where
  size = 0
  {-# INLINABLE size #-}

instance Sized f => Sized (M1 i c f) where
  size = size @f
  {-# INLINABLE size #-}

instance (Sized g, Sized f) => Sized (g :.: f) where
  size = size @g * size @f
  {-# INLINABLE size #-}

instance (Sized f, Sized g) => Sized (f :*: g) where
  size = size @f + size @g
  {-# INLINABLE size #-}
