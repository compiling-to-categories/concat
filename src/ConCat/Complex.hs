{-# LANGUAGE CPP, TypeOperators, TypeFamilies #-}
{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

#define CustomComplex

#if !defined CustomComplex
{-# OPTIONS_GHC -fno-warn-orphans #-} -- for HasRep
#endif

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Complex
-- Copyright   :  (c) 2015 Conal Elliott and David Banas
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Simplified Complex type
----------------------------------------------------------------------

module ConCat.Complex (Complex(..)) where

#if defined CustomComplex
import Control.Applicative (liftA2)
import Data.Typeable
import Data.Data
import Test.QuickCheck (Arbitrary(..),CoArbitrary(..))
#else
import Data.Complex
#endif

#if defined CustomComplex
infixl 1 :+
data Complex a = a :+ a deriving (Functor,Eq,Show,Typeable,Data,Ord)

-- | The nonnegative magnitude of a complex number.
-- {-# SPECIALISE magnitude :: Complex Double -> Double #-}
magnitude :: (RealFloat a) => Complex a -> a

magnitude (x:+y) = sqrt (x*x + y*y)

-- From Data.Complex

-- magnitude (x:+y) =  scaleFloat k
--                      (sqrt (sqr (scaleFloat mk x) + sqr (scaleFloat mk y)))
--                     where k  = max (exponent x) (exponent y)
--                           mk = - k
--                           sqr z = z * z

-- | The phase of a complex number, in the range @(-'pi', 'pi']@.
-- If the magnitude is zero, then so is the phase.
-- {-# SPECIALISE phase :: Complex Double -> Double #-}
phase :: (RealFloat a) => Complex a -> a
phase (0 :+ 0)   = 0            -- SLPJ July 97 from John Peterson
phase (x:+y)     = atan2 y x

instance  (RealFloat a) => Num (Complex a)  where
    -- {-# SPECIALISE instance Num (Complex Float) #-}
    -- {-# SPECIALISE instance Num (Complex Double) #-}
    (x:+y) + (x':+y')   =  (x+x') :+ (y+y')
    (x:+y) - (x':+y')   =  (x-x') :+ (y-y')
    (x:+y) * (x':+y')   =  (x*x'-y*y') :+ (x*y'+y*x')
    negate (x:+y)       =  negate x :+ negate y
    abs z               =  magnitude z :+ 0
    signum (0:+0)       =  0
    signum z@(x:+y)     =  x/r :+ y/r  where r = magnitude z
    fromInteger n       =  fromInteger n :+ 0
    {-# INLINE (+)         #-}
    {-# INLINE (-)         #-}
    {-# INLINE (*)         #-}
    {-# INLINE negate      #-}
    {-# INLINE abs         #-}
    {-# INLINE signum      #-}
    {-# INLINE fromInteger #-}

instance  (RealFloat a) => Fractional (Complex a)  where
    -- {-# SPECIALISE instance Fractional (Complex Float) #-}
    -- {-# SPECIALISE instance Fractional (Complex Double) #-}
    recip z@(x:+y) = x/mag :+ (-y)/mag where mag = magnitude z
--     (x:+y) / (x':+y')   =  (x*x''+y*y'') / d :+ (y*x''-x*y'') / d
--                            where x'' = scaleFloat k x'
--                                  y'' = scaleFloat k y'
--                                  k   = - max (exponent x') (exponent y')
--                                  d   = x'*x'' + y'*y''

    fromRational a      =  fromRational a :+ 0

instance  (RealFloat a) => Floating (Complex a) where
    -- {-# SPECIALISE instance Floating (Complex Float) #-}
    -- {-# SPECIALISE instance Floating (Complex Double) #-}
    pi             =  pi :+ 0
    exp (x:+y)     =  expx * cos y :+ expx * sin y
                      where expx = exp x
    log z          =  log (magnitude z) :+ phase z

    sqrt (0:+0)    =  0
    sqrt z@(x:+y)  =  u :+ (if y < 0 then -v else v)
                      where (u,v) = if x < 0 then (v',u') else (u',v')
                            v'    = abs y / (u'*2)
                            u'    = sqrt ((magnitude z + abs x) / 2)

    sin (x:+y)     =  sin x * cosh y :+ cos x * sinh y
    cos (x:+y)     =  cos x * cosh y :+ (- sin x * sinh y)
    tan (x:+y)     =  (sinx*coshy:+cosx*sinhy)/(cosx*coshy:+(-sinx*sinhy))
                      where sinx  = sin x
                            cosx  = cos x
                            sinhy = sinh y
                            coshy = cosh y

    sinh (x:+y)    =  cos y * sinh x :+ sin  y * cosh x
    cosh (x:+y)    =  cos y * cosh x :+ sin y * sinh x
    tanh (x:+y)    =  (cosy*sinhx:+siny*coshx)/(cosy*coshx:+siny*sinhx)
                      where siny  = sin y
                            cosy  = cos y
                            sinhx = sinh x
                            coshx = cosh x

    asin z@(x:+y)  =  y':+(-x')
                      where  (x':+y') = log (((-y):+x) + sqrt (1 - z*z))
    acos z         =  y'':+(-x'')
                      where (x'':+y'') = log (z + ((-y'):+x'))
                            (x':+y')   = sqrt (1 - z*z)
    atan z@(x:+y)  =  y':+(-x')
                      where (x':+y') = log (((1-y):+x) / sqrt (1+z*z))

    asinh z        =  log (z + sqrt (1+z*z))
    acosh z        =  log (z + (z+1) * sqrt ((z-1)/(z+1)))
    atanh z        =  0.5 * log ((1.0+z) / (1.0-z))

instance Arbitrary a => Arbitrary (Complex a) where
  arbitrary = liftA2 (:+) arbitrary arbitrary
  shrink (x :+ y) = map (uncurry (:+)) (shrink (x,y))

instance CoArbitrary a => CoArbitrary (Complex a) where
  coarbitrary (x :+ y) = coarbitrary x . coarbitrary y

#endif
