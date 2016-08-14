{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances
  , FlexibleInstances, MultiParamTypeClasses, CPP  #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  Basis
-- Copyright   :  (c) Conal Elliott 2008-2016
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Basis of a vector space, as an associated type
----------------------------------------------------------------------

module Basis (HasBasis(..), linearCombo, recompose) where

-- import Control.Applicative ((<$>))
import Control.Arrow (first)
import Data.Ratio
import Foreign.C.Types (CFloat, CDouble)
-- import Data.Either

import Data.AdditiveGroup

import Ring

class Ring v => HasBasis v where
  -- | Representation of the canonical basis for @v@
  type Basis v :: *
  -- | Interpret basis rep as a vector
  basisValue   :: Basis v -> v
  -- | Extract coordinates
  decompose    :: v -> [(Basis v, Scalar v)]
  -- | Experimental version.  More elegant definitions, and friendly to
  -- infinite-dimensional vector spaces.
  decompose'   :: v -> (Basis v -> Scalar v)

-- Defining property: recompose . decompose == id

-- Turn a basis decomposition back into a vector.
recompose :: HasBasis v => [(Basis v, Scalar v)] -> v
recompose = linearCombo . fmap (first basisValue)

-- recompose ps = linearCombo (first basisValue <$> ps)

-- I don't know how to define
-- 
--   recompose' :: HasBasis v => (Basis v -> Scalar v) -> v
-- 
-- However, I don't seem to use recompose anywhere.
-- I don't even use basisValue or decompose.

#define ScalarTypeCon(con,t) \
  instance con => HasBasis (t) where \
    { type Basis (t) = () \
    ; basisValue ()  = 1 \
    ; decompose s    = [((),s)] \
    ; decompose' s   = const s }

#define ScalarType(t) ScalarTypeCon((),t)

ScalarType(Float)
ScalarType(Double)
ScalarType(CFloat)
ScalarType(CDouble)

ScalarTypeCon(Integral a, Ratio a)

instance ( HasBasis u, s ~ Scalar u
         , HasBasis v, s ~ Scalar v )
      => HasBasis (u,v) where
  type Basis (u,v)     = Basis u `Either` Basis v
  basisValue (Left  a) = (basisValue a, zeroV)
  basisValue (Right b) = (zeroV, basisValue b)
  decompose  (u,v)     = decomp2 Left u ++ decomp2 Right v
  decompose' (u,v)     = decompose' u `either` decompose' v


decomp2 :: HasBasis w => (Basis w -> b) -> w -> [(b, Scalar w)]
decomp2 inject = fmap (first inject) . decompose

instance ( HasBasis u, s ~ Scalar u
         , HasBasis v, s ~ Scalar v
         , HasBasis w, s ~ Scalar w )
      => HasBasis (u,v,w) where
  type Basis (u,v,w) = Basis (u,(v,w))
  basisValue         = unnest3 . basisValue
  decompose          = decompose  . nest3
  decompose'         = decompose' . nest3

unnest3 :: (a,(b,c)) -> (a,b,c)
unnest3 (a,(b,c)) = (a,b,c)

nest3 :: (a,b,c) -> (a,(b,c))
nest3 (a,b,c) = (a,(b,c))


-- instance (Eq a, HasBasis u) => HasBasis (a -> u) where
--   type Basis (a -> u) = (a, Basis u)
--   basisValue (a,b) = f
--     where f a' | a == a'   = bv
--                | otherwise = zeroV
--           bv = basisValue b
--   decompose = error "decompose: not defined on functions"
--   decompose' g (a,b) = decompose' (g a) b


-- Simpler but less efficient:
-- 
--   basisValue (a,b) a' | a == a'   = basisValue b
--                       | otherwise = zeroV

-- Just for pointless perversion points:
-- 
--   decompose' g = uncurry (\ a b -> decompose' (g a) b)
--   decompose' g = uncurry (\ a -> decompose' (g a))
--   decompose' g = uncurry (decompose' . g)
--   decompose' = uncurry . fmap decompose'
--   decompose' = (fmap uncurry) (fmap decompose')


{-

---- Testing

t1 = basisValue () :: Float
t2 = basisValue () :: Double
t3 = basisValue (Right ()) :: (Float,Double)
t4 = basisValue (Right (Left ())) :: (Float,Double,Float)

-}
