{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures   #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Scan
-- Copyright   :  (c) 2016 Conal Elliott
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Parallel scan
----------------------------------------------------------------------

module ConCat.Scan
  ( LScan(..)
  , lscanT, lscanTraversable
  , lsums, lproducts, lAlls, lAnys, lParities
  , multiples, powers, iota
  ) where

import Prelude hiding (zip,unzip,zipWith)

import Data.Monoid ((<>),Sum(..),Product(..),All(..),Any(..))
import Control.Arrow ((***),first)
import Data.Traversable (mapAccumL)
import Data.Tuple (swap)
import GHC.Generics

import Control.Newtype (Newtype(..))

import Data.Key
import Data.Pointed

import ConCat.Misc ((:*),Parity(..),absurdF) -- , Unop
-- import ConCat.Misc (absurdF)

class Functor f => LScan f where
  lscan :: forall a. Monoid a => f a -> f a :* a
  default lscan :: (Generic1 f, LScan (Rep1 f), Monoid a) => f a -> f a :* a
  lscan = first to1 . lscan . from1
  -- Temporary hack to avoid newtype-like representation. Still needed?
  lscanDummy :: f a
  lscanDummy = undefined
--   lscanWork, lscanDepth :: forall a. MappendStats a => Int

-- TODO: Try removing lscanDummy and the comment and recompiling with reification

-- | Traversable version (sequential)
lscanT :: Traversable t => (b -> a -> b) -> b -> t a -> (t b,b)
lscanT op e = swap . mapAccumL (\ b a -> (b `op` a,b)) e
{-# INLINABLE lscanT #-}

lscanTraversable :: Traversable f => forall a. Monoid a => f a -> f a :* a
lscanTraversable = lscanT mappend mempty
{-# INLINABLE lscanTraversable #-}

{--------------------------------------------------------------------
    Monoid specializations
--------------------------------------------------------------------}

-- Left-scan via a 'Newtype'
lscanAla :: forall n o f. (Newtype n, o ~ O n, LScan f, Monoid n)
         => f o -> f o :* o
lscanAla = (fmap unpack *** unpack) . lscan . fmap (pack @n)

-- lscanAla k = underF k lscan
-- lscanAla _k = fmap unpack . lscan . fmap (pack :: o -> n)

lsums :: forall f a. (LScan f, Num a) => f a -> (f a, a)
lsums = lscanAla @(Sum a)
{-# INLINABLE lsums #-}

lproducts :: forall f a. (LScan f, Num a) => f a -> f a :* a
lproducts = lscanAla @(Product a)
{-# INLINABLE lproducts #-}

lAlls :: LScan f => f Bool -> (f Bool, Bool)
lAlls = lscanAla @All
{-# INLINABLE lAlls #-}

lAnys :: LScan f => f Bool -> (f Bool, Bool)
lAnys = lscanAla @Any
{-# INLINABLE lAnys #-}

lParities :: LScan f => f Bool -> (f Bool, Bool)
lParities = lscanAla @Parity
{-# INLINABLE lParities #-}

multiples :: (LScan f, Pointed f, Num a) => a -> f a :* a
multiples = lsums . point

powers :: (LScan f, Pointed f, Num a) => a -> f a :* a
powers = lproducts . point

-- | Numbers from 0 to n (size of f). Named for APL iota operation (but 0 based).
iota :: (LScan f, Pointed f, Num a) => f a :* a
iota = multiples 1

{--------------------------------------------------------------------
    Work and depth
--------------------------------------------------------------------}

-- class Monoid o => MappendStats o where
--   mappendWork, mappendDepth :: Int
--   mappendWork = 1
--   mappendDepth = 1

-- instance Num a => MappendStats (Sum     a)
-- instance Num a => MappendStats (Product a)

{--------------------------------------------------------------------
    Generic support
--------------------------------------------------------------------}

instance LScan V1 where
  lscan = absurdF
--   lscanWork = 0
--   lscanDepth = 0

instance LScan U1 where
  lscan U1 = (U1, mempty)
--   lscanWork = 0
--   lscanDepth = 0

instance LScan (K1 i c) where
  lscan w@(K1 _) = (w, mempty)
--   lscanWork = 0
--   lscanDepth = 0

instance LScan Par1 where
  lscan (Par1 a) = (Par1 mempty, a)
--   lscanWork = 0
--   lscanDepth = 0

-- foo :: Int
-- foo = lscanWork @Par1 @(Sum Int)

instance (LScan f, LScan g) => LScan (f :+: g) where
  lscan (L1 fa) = first L1 (lscan fa)
  lscan (R1 ga) = first R1 (lscan ga)
--   lscanWork, lscanDepth :: forall a. MappendStats a => Int
--   lscanWork = max (lscanWork @f @a) (lscanWork @g @a)
--   lscanDepth = max (lscanDepth @f @a) (lscanDepth @g @a)

-- GHC objects:
-- 
--     • Could not deduce (MappendStats a0)
--       from the context: (LScan f, LScan g)
--         bound by the instance declaration
--         at /Users/conal/Haskell/shaped-types/src/ConCat/Scan.hs:157:10-46
--       or from: MappendStats a
--         bound by the type signature for:
--                    lscanWork :: MappendStats a => Int
--         at /Users/conal/Haskell/shaped-types/src/ConCat/Scan.hs:160:28-58
--       The type variable ‘a0’ is ambiguous
--
-- I wonder if ScopedTypeVariables is failing here

instance (LScan f, LScan g) => LScan (f :*: g) where
  lscan (fa :*: ga) = (fa' :*: ((fx <>) <$> ga'), fx <> gx)
   where
     (fa', fx) = lscan fa
     (ga', gx) = lscan ga
--   lscanWork :: 
--   lscanWork = lscanWork @f + lscanWork @g + mappendWork 

-- Alternatively,

--   lscan (fa :*: ga) = (fa' :*: ga', gx)
--    where
--      (fa', fx) =               lscan fa
--      (ga', gx) = mapl (fx <>) (lscan ga)

instance (LScan g, LScan f, Zip g) =>  LScan (g :.: f) where
  lscan (Comp1 gfa) = (Comp1 (zipWith adjustl tots' gfa'), tot)
   where
     (gfa', tots)  = unzip (lscan <$> gfa)
     (tots',tot)   = lscan tots
     adjustl t     = fmap (t <>)

-- TODO: maybe zipWith (fmap . mappend) tots' gfa'

instance LScan f => LScan (M1 i c f) where
  lscan (M1 as) = first M1 (lscan as)

unzip :: forall f a b. Functor f => f (a :* b) -> f a :* f b
unzip ps = (fst <$> ps, snd <$> ps)

