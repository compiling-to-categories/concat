{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- | Linear maps as constrained category

module Ring where

import Prelude hiding (id,(.))
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)
import Data.Ratio
-- import Data.Complex hiding (magnitude)

import Data.AdditiveGroup

import Misc
import ConCat

infixr 7 *^

-- | Vector space @v@.
class (HasConseq Ring v, AdditiveGroup v) => Ring v where
  type Scalar v :: *
  -- | Scale a vector
  (*^) :: Scalar v -> v -> v

infixr 7 <.>

-- | Adds inner (dot) products.
class (Ring v, AdditiveGroup (Scalar v)) => InnerSpace v where
  -- | Inner/dot product
  (<.>) :: v -> v -> Scalar v

infixr 7 ^/
infixl 7 ^*

-- | Vector divided by scalar
(^/) :: (Ring v, s ~ Scalar v, Fractional s) => v -> s -> v
v ^/ s = (1/s) *^ v

-- | Vector multiplied by scalar
(^*) :: (Ring v, s ~ Scalar v) => v -> s -> v
(^*) = flip (*^)

-- | Linear interpolation between @a@ (when @t==0@) and @b@ (when @t==1@).

-- lerp :: (Ring v, s ~ Scalar v, Num s) => v -> v -> s -> v
lerp :: Ring v => v -> v -> Scalar v -> v
lerp a b t = a ^+^ t *^ (b ^-^ a)

-- | Linear combination of vectors
linearCombo :: Ring v => [(v,Scalar v)] -> v
linearCombo ps = sumV [v ^* s | (v,s) <- ps]

-- | Square of the length of a vector.  Sometimes useful for efficiency.
-- See also 'magnitude'.
magnitudeSq :: (InnerSpace v, s ~ Scalar v) => v -> s
magnitudeSq v = v <.> v

-- | Length of a vector.   See also 'magnitudeSq'.
magnitude :: (InnerSpace v, s ~ Scalar v, Floating s) =>  v -> s
magnitude = sqrt . magnitudeSq

-- | Vector in same direction as given one but with length of one.  If
-- given the zero vector, then return it.
normalized :: (InnerSpace v, s ~ Scalar v, Floating s) =>  v -> v
normalized v = v ^/ magnitude v

-- | @project u v@ computes the projection of @v@ onto @u@.
project :: (InnerSpace v, s ~ Scalar v, Fractional s) => v -> v -> v
project u v = ((v <.> u) / magnitudeSq u) *^ u

#define ScalarType(t) \
  instance HasConseq Ring (t) ; \
  instance Ring (t) where \
    { type Scalar t = (t) \
    ; (*^) = (*) } ; \
  instance InnerSpace (t) where (<.>) = (*)

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

instance Integral a => Ring (Ratio a) where
  type Scalar (Ratio a) = Ratio a
  (*^) = (*)
instance Integral a => InnerSpace (Ratio a) where (<.>) = (*)

type instance Conseq Ring (Ratio a) = ()
instance HasConseq Ring (Ratio a)

-- instance (RealFloat v, Ring v) => Ring (Complex v) where
--   type Scalar (Complex v) = Scalar v
--   s*^(u :+ v) = s*^u :+ s*^v

-- instance (RealFloat v, InnerSpace v)
--      => InnerSpace (Complex v) where
--   (u :+ v) <.> (u' :+ v') = (u <.> u') ^+^ (v <.> v')

instance ( Ring u, s ~ Scalar u
         , Ring v, s ~ Scalar v )
      => Ring (u,v) where
  type Scalar (u,v) = Scalar u
  s *^ (u,v) = (s*^u,s*^v)

instance ( InnerSpace u, s ~ Scalar u
         , InnerSpace v, s ~ Scalar v )
    => InnerSpace (u,v) where
  (u,v) <.> (u',v') = (u <.> u') ^+^ (v <.> v')

instance ( Ring u, s ~ Scalar u
         , Ring v, s ~ Scalar v
         , Ring w, s ~ Scalar w )
    => Ring (u,v,w) where
  type Scalar (u,v,w) = Scalar u
  s *^ (u,v,w) = (s*^u,s*^v,s*^w)

instance ( InnerSpace u, s ~ Scalar u
         , InnerSpace v, s ~ Scalar v
         , InnerSpace w, s ~ Scalar w )
    => InnerSpace (u,v,w) where
  (u,v,w) <.> (u',v',w') = u<.>u' ^+^ v<.>v' ^+^ w<.>w'

instance ( Ring u, s ~ Scalar u
         , Ring v, s ~ Scalar v
         , Ring w, s ~ Scalar w
         , Ring x, s ~ Scalar x )
    => Ring (u,v,w,x) where
  type Scalar (u,v,w,x) = Scalar u
  s *^ (u,v,w,x) = (s*^u,s*^v,s*^w,s*^x)

instance ( InnerSpace u, s ~ Scalar u
         , InnerSpace v, s ~ Scalar v
         , InnerSpace w, s ~ Scalar w
         , InnerSpace x, s ~ Scalar x )
    => InnerSpace (u,v,w,x) where
  (u,v,w,x) <.> (u',v',w',x') = u<.>u' ^+^ v<.>v' ^+^ w<.>w' ^+^ x<.>x'
