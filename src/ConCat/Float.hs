{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Simple Float and Double wrappers as a temporary workaround for failure to
-- find numeric instances for Float and Double.

module ConCat.Float (Float,Double) where

import Prelude hiding (Float,Double)
import qualified Prelude as P

#if 0

type Float  = P.Float
type Double = P.Double

#else

import Control.Arrow (first)

newtype Float = F P.Float deriving (Eq,Ord,Num,Fractional,Floating)

instance Show Float where showsPrec p (F x) = showsPrec p x
instance Read Float where readsPrec p = (map . first) F . readsPrec p

newtype Double = D P.Double deriving (Eq,Ord,Num,Fractional,Floating)

instance Show Double where showsPrec p (D x) = showsPrec p x
instance Read Double where readsPrec p = (map . first) D . readsPrec p

#endif
