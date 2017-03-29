{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DefaultSignatures #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Simple Float and Double wrappers as a temporary workaround for failure to
-- find numeric instances for Float and Double.

module ConCat.Float where

import Prelude hiding (Float,Double)
import qualified Prelude as P

#if 1

type Float  = P.Float
type Double = P.Double

#if 1

type NumZ = Num
fromIntegerZ :: Num a => Integer -> a
negateZ :: Num a => a -> a
addZ :: Num a => a -> a -> a
subZ :: Num a => a -> a -> a
mulZ :: Num a => a -> a -> a
powIZ :: (Num a, Integral n) => a -> n -> a
fromIntegerZ = fromInteger
negateZ = negate
addZ = (+)
subZ = (-)
mulZ = (*)
powIZ = (^)

type FractionalZ = Fractional
recipZ :: Fractional a => a -> a
divideZ :: Fractional a => a -> a -> a
recipZ = recip
divideZ = (/)

type FloatingZ   = Floating
expZ :: Floating a => a -> a
cosZ :: Floating a => a -> a
sinZ :: Floating a => a -> a
expZ = exp
cosZ = cos
sinZ = sin

type ShowZ = Show
showZ :: Show a => a -> String
showZ = show

#else

class NumZ a where
  fromIntegerZ :: Integer -> a
  negateZ :: a -> a
  addZ, subZ, mulZ :: a -> a -> a
  powIZ :: Integral n => a -> n -> a
  default fromIntegerZ :: Num a => Integer -> a
  default negateZ :: Num a => a -> a
  default addZ :: Num a => a -> a -> a
  default subZ :: Num a => a -> a -> a
  default mulZ :: Num a => a -> a -> a
  default powIZ :: (Num a, Integral n) => a -> n -> a
  fromIntegerZ = fromInteger
  negateZ = negate
  addZ = (+)
  subZ = (-)
  mulZ = (*)
  powIZ = (^)

instance NumZ Int
instance NumZ Float
instance NumZ Double

class NumZ a => FractionalZ a where
  recipZ :: a -> a
  divideZ :: a -> a -> a
  default recipZ :: Fractional a => a -> a
  default divideZ :: Fractional a => a -> a -> a
  recipZ = recip
  divideZ = (/)

instance FractionalZ Float
instance FractionalZ Double

class Fractional a => FloatingZ a where
  expZ, cosZ, sinZ :: a -> a
  default expZ :: Floating a => a -> a
  default cosZ :: Floating a => a -> a
  default sinZ :: Floating a => a -> a
  expZ = exp
  cosZ = cos
  sinZ = sin

instance FloatingZ Float
instance FloatingZ Double

class ShowZ a where
  showZ :: a -> String
  default showZ :: Show a => a -> String
  showZ = show

instance ShowZ ()
instance ShowZ Bool
instance ShowZ Int
instance ShowZ Float
instance ShowZ Double

#endif

#else

import Control.Arrow (first)

newtype Float = F P.Float deriving (Eq,Ord,Num,Fractional,Floating)

instance Show Float where showsPrec p (F x) = showsPrec p x
instance Read Float where readsPrec p = (map . first) F . readsPrec p

newtype Double = D P.Double deriving (Eq,Ord,Num,Fractional,Floating)

instance Show Double where showsPrec p (D x) = showsPrec p x
instance Read Double where readsPrec p = (map . first) D . readsPrec p

#endif
