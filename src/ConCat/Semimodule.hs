{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Linear maps as constrained category

module Semimodule where

import Control.Applicative (liftA2)
import Data.Ratio
import Foreign.C.Types
  (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)
-- import Data.Complex hiding (magnitude)

import Additive

infixr 7 *^

-- | A semimodule, which is like module, but over a semiring rather than a ring.
class Additive v => Semimodule v where
  type Scalar v :: *
  (*^) :: Scalar v -> v -> v

infixr 7 ^*^

-- | Adds inner (dot) products.
class (Semimodule v, Additive (Scalar v)) => InnerSpace v where
  -- | Inner/dot product
  (^*^) :: v -> v -> Scalar v

-- Semimodule over a given scalar type
type Mod s u = (Semimodule u, Scalar u ~ s)

-- Inner space over a given scalar type
type Inner s u = (InnerSpace u, Scalar u ~ s)

infixr 7 ^/
infixl 7 ^*

-- | Vector divided by scalar
(^/) :: (Mod s v, Fractional s) => v -> s -> v
v ^/ s = (1/s) *^ v

-- | Vector multiplied by scalar
(^*) :: Mod s v => v -> s -> v
(^*) = flip (*^)

-- | Linear interpolation between @a@ (when @t==0@) and @b@ (when @t==1@).

-- lerp :: Semimodule v => v -> v -> Scalar v -> v
-- lerp a b t = a ^+^ t *^ (b ^-^ a)

-- | Linear combination of vectors
linearCombo :: Semimodule v => [(v,Scalar v)] -> v
linearCombo ps = add [v ^* s | (v,s) <- ps]

-- | Square of the length of a vector.  Sometimes useful for efficiency.
-- See also 'magnitude'.
magnitudeSq :: Inner s v => v -> s
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

-- -- Oops. What scalar type to use?
-- instance Semimodule () where
--   type Scalar () = ()
--   s *^ () = ()

#define ScalarType(t) \
  instance Semimodule (t) where \
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

instance Integral a => Semimodule (Ratio a) where
  type Scalar (Ratio a) = Ratio a
  (*^) = (*)
instance Integral a => InnerSpace (Ratio a) where (^*^) = (*)

-- instance (RealFloat v, Semimodule v) => Semimodule (Complex v) where
--   type Scalar (Complex v) = Scalar v
--   s*^(u :+ v) = s*^u :+ s*^v

-- instance (RealFloat v, InnerSpace v)
--      => InnerSpace (Complex v) where
--   (u :+ v) ^*^ (u' :+ v') = (u ^*^ u') ^+^ (v ^*^ v')

instance (Mod s u, Mod s v) => Semimodule (u,v) where
  type Scalar (u,v) = Scalar u
  s *^ (u,v) = (s*^u,s*^v)

instance (Inner s u, Inner s v) => InnerSpace (u,v) where
  (u,v) ^*^ (u',v') = (u ^*^ u') ^+^ (v ^*^ v')

instance (Mod s u, Mod s v, Mod s w) => Semimodule (u,v,w) where
  type Scalar (u,v,w) = Scalar u
  s *^ (u,v,w) = (s*^u,s*^v,s*^w)

instance (Inner s u, Inner s v, Inner s w) => InnerSpace (u,v,w) where
  (u,v,w) ^*^ (u',v',w') = u^*^u' ^+^ v^*^v' ^+^ w^*^w'

instance (Mod s u, Mod s v, Mod s w, Mod s x) => Semimodule (u,v,w,x) where
  type Scalar (u,v,w,x) = Scalar u
  s *^ (u,v,w,x) = (s*^u,s*^v,s*^w,s*^x)

instance (Inner s u, Inner s v, Inner s w, Inner s x)
      => InnerSpace (u,v,w,x) where
  (u,v,w,x) ^*^ (u',v',w',x') = u^*^u' ^+^ v^*^v' ^+^ w^*^w' ^+^ x^*^x'


instance Semimodule v => Semimodule (a -> v) where
  type Scalar (a -> v) = Scalar v
  (*^) s = fmap (s *^)

-- For an InnerSpace instance, I guess we'd need to sum or integrate over the
-- domain.
