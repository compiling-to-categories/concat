{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | 

module ConCat.Distrib where

import Prelude hiding (id,(.))

import Data.Map -- (Map,fromList,toList,singleton,unionsWith,mapKeys)
-- import qualified Data.Map as M

import ConCat.Misc (R)
import ConCat.AltCat
import qualified ConCat.Category

newtype Distrib a b = Distrib (a -> Map b R)

-- TODO: generalize Distrib to a category transformer

-- TODO: Maybe generalize to semirings

exactly :: (a -> b) -> Distrib a b
-- exactly f = Distrib (\ a -> singleton (f a) 1)
exactly f = Distrib (flip singleton 1 . f)

instance Category Distrib where
  type Ok Distrib = Ord
  id = exactly id
  Distrib g . Distrib f = Distrib h
   where
     h a = unionsWith (+) [ (p *) <$> g b | (b,p) <- toList (f a) ]

instance AssociativePCat Distrib where
  lassocP = exactly lassocP
  rassocP = exactly rassocP

instance BraidedPCat Distrib where swapP = exactly swapP

instance MonoidalPCat Distrib where
  Distrib f *** Distrib g = Distrib h
   where
     h (a,b) = fromList [ ((c,d),p*q) | (c,p) <- toList (f a), (d,q) <- toList (g b) ]
  -- We could default first and second, but the following may be more efficient:
  first  (Distrib f) = Distrib (\ (a,b) -> mapKeys (,b) (f a))
  second (Distrib g) = Distrib (\ (a,b) -> mapKeys (a,) (g b))
     
instance ProductCat Distrib where
  exl = exactly exl
  exr = exactly exr
  dup = exactly dup

-- TODO: coproducts and closure.

instance AssociativeSCat Distrib where
  lassocS = exactly lassocS
  rassocS = exactly rassocS

instance BraidedSCat Distrib where swapS = exactly swapS

instance MonoidalSCat Distrib where
  Distrib f +++ Distrib g = Distrib h
   where
     h = mapKeys Left . f ||| mapKeys Right . g
  -- We could default left and right, but the following may be more efficient:
  left  (Distrib f) = Distrib (mapKeys Left . f ||| flip singleton 1 . Right)
  right (Distrib g) = Distrib (flip singleton 1 . Left ||| mapKeys Right . g)

instance CoproductCat Distrib where
  inl = exactly inl
  inr = exactly inr
  jam = exactly jam

instance Num a => ScalarCat Distrib a where
  scale s = exactly (scale s)

-- TODO: CoproductPCat, DistribCat, ClosedCat.
