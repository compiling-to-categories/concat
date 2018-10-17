{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | A category of probabilistic functions

module ConCat.Distribution where

import Prelude hiding (id,(.))

import Data.Map

import ConCat.Misc (R)
import ConCat.AltCat
import qualified ConCat.Category

-- | Distribution category
newtype Dist a b = Dist (a -> Map b R)

-- TODO: generalize Dist to a category transformer

-- | The one category-specific operation.
distrib :: (a -> Map b R) -> Dist a b
distrib = Dist

-- TODO: Perhaps replace 'distrib' with a simpler alternative.

-- | Embed a regular deterministic function
exactly :: (a -> b) -> Dist a b
exactly f = Dist (flip singleton 1 . f)
-- exactly f = Dist (\ a -> singleton (f a) 1)

instance Category Dist where
  type Ok Dist = Ord
  id = exactly id
  Dist g . Dist f = Dist h
   where
     h a = unionsWith (+) [ (p *) <$> g b | (b,p) <- toList (f a) ]

instance AssociativePCat Dist where
  lassocP = exactly lassocP
  rassocP = exactly rassocP

instance BraidedPCat Dist where swapP = exactly swapP

instance MonoidalPCat Dist where
  Dist f *** Dist g = Dist h
   where
     h (a,b) = fromList [ ((c,d),p*q) | (c,p) <- toList (f a), (d,q) <- toList (g b) ]
  -- We could default first and second, but the following may be more efficient:
  first  (Dist f) = Dist (\ (a,b) -> mapKeys (,b) (f a))
  second (Dist g) = Dist (\ (a,b) -> mapKeys (a,) (g b))
     
instance ProductCat Dist where
  exl = exactly exl
  exr = exactly exr
  dup = exactly dup

instance AssociativeSCat Dist where
  lassocS = exactly lassocS
  rassocS = exactly rassocS

instance BraidedSCat Dist where swapS = exactly swapS

instance MonoidalSCat Dist where
  Dist f +++ Dist g = Dist h
   where
     h = mapKeys Left . f ||| mapKeys Right . g
  -- We could default left and right, but the following may be more efficient:
  left  (Dist f) = Dist (mapKeys Left . f ||| flip singleton 1 . Right)
  right (Dist g) = Dist (flip singleton 1 . Left ||| mapKeys Right . g)

-- TODO: test whether the first/second and left/right definitions produce more
-- efficient implementations than the defaults. Can GHC optimize away the
-- singleton dictionaries in the defaults?

instance CoproductCat Dist where
  inl = exactly inl
  inr = exactly inr
  jam = exactly jam

instance Num a => ScalarCat Dist a where
  scale s = exactly (scale s)

-- TODO: CoproductPCat, DistribCat, ClosedCat.

-- TODO: vocabulary specific to this category.


