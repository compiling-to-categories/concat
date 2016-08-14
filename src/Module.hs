{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

-- | Linear maps as constrained category

module Module where

import Prelude hiding (id,(.))
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)
import Data.Ratio
-- import Data.Complex hiding (magnitude)

import Data.AdditiveGroup

import ConCat

infixr 7 *^

-- | Vector space @v@.
class AdditiveGroup v => Module v where
  type Scalar v :: *
  -- | Scale a vector
  (*^) :: Scalar v -> v -> v

infixr 7 ^*^

-- | Adds inner (dot) products.
class (Module v, AdditiveGroup (Scalar v)) => InnerSpace v where
  -- | Inner/dot product
  (^*^) :: v -> v -> Scalar v

infixr 7 ^/
infixl 7 ^*

-- Module over a given scalar type
type Mod s u = (Module u, Scalar u ~ s)

-- Inner space over a given scalar type
type Inner s u = (InnerSpace u, Scalar u ~ s)

-- | Vector divided by scalar
(^/) :: (Mod s v, Fractional s) => v -> s -> v
v ^/ s = (1/s) *^ v

-- | Vector multiplied by scalar
(^*) :: (Mod s v) => v -> s -> v
(^*) = flip (*^)

-- | Linear interpolation between @a@ (when @t==0@) and @b@ (when @t==1@).

lerp :: Module v => v -> v -> Scalar v -> v
lerp a b t = a ^+^ t *^ (b ^-^ a)

-- | Linear combination of vectors
linearCombo :: Module v => [(v,Scalar v)] -> v
linearCombo ps = sumV [v ^* s | (v,s) <- ps]

-- | Square of the length of a vector.  Sometimes useful for efficiency.
-- See also 'magnitude'.
magnitudeSq :: (Inner s v) => v -> s
magnitudeSq v = v ^*^ v

-- | Length of a vector.   See also 'magnitudeSq'.
magnitude :: (Inner s v, Floating s) =>  v -> s
magnitude = sqrt . magnitudeSq

-- | Vector in same direction as given one but with length of one.  If
-- given the zero vector, then return it.
normalized :: (Inner s v, Floating s) =>  v -> v
normalized v = v ^/ magnitude v

-- | @project u v@ computes the projection of @v@ onto @u@.
project :: (Inner s v, Fractional s) => v -> v -> v
project u v = ((v ^*^ u) / magnitudeSq u) *^ u

#define ScalarType(t) \
  instance Module (t) where \
    { type Scalar t = (t) \
    ; (*^) = (*) } ; \
  instance InnerSpace (t) where (^*^) = (*)

ScalarType(Int)
ScalarType(Integer)
ScalarType(Float)
ScalarType(Double)
ScalarType(CSChar)
ScalarType(CInt)
ScalarType(CShort)
ScalarType(CLong)
ScalarType(CLLong)
ScalarType(CIntMax)
ScalarType(CDouble)
ScalarType(CFloat)

instance Integral a => Module (Ratio a) where
  type Scalar (Ratio a) = Ratio a
  (*^) = (*)
instance Integral a => InnerSpace (Ratio a) where (^*^) = (*)

-- instance (RealFloat v, Module v) => Module (Complex v) where
--   type Scalar (Complex v) = Scalar v
--   s*^(u :+ v) = s*^u :+ s*^v

-- instance (RealFloat v, InnerSpace v)
--      => InnerSpace (Complex v) where
--   (u :+ v) ^*^ (u' :+ v') = (u ^*^ u') ^+^ (v ^*^ v')

instance (Mod s u, Mod s v) => Module (u,v) where
  type Scalar (u,v) = Scalar u
  s *^ (u,v) = (s*^u,s*^v)

instance (Inner s u, Inner s v) => InnerSpace (u,v) where
  (u,v) ^*^ (u',v') = (u ^*^ u') ^+^ (v ^*^ v')

instance (Mod s u, Mod s v, Mod s w) => Module (u,v,w) where
  type Scalar (u,v,w) = Scalar u
  s *^ (u,v,w) = (s*^u,s*^v,s*^w)

instance (Inner s u, Inner s v, Inner s w) => InnerSpace (u,v,w) where
  (u,v,w) ^*^ (u',v',w') = u^*^u' ^+^ v^*^v' ^+^ w^*^w'

instance (Mod s u, Mod s v, Mod s w, Mod s x) => Module (u,v,w,x) where
  type Scalar (u,v,w,x) = Scalar u
  s *^ (u,v,w,x) = (s*^u,s*^v,s*^w,s*^x)

instance (Inner s u, Inner s v, Inner s w, Inner s x)
      => InnerSpace (u,v,w,x) where
  (u,v,w,x) ^*^ (u',v',w',x') = u^*^u' ^+^ v^*^v' ^+^ w^*^w' ^+^ x^*^x'
