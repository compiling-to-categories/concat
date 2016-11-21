{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Simple Float and Double wrappers as a temporary workaround for difficulty finding
-- numeric instances for Float and Double.

module ConCat.Float (Float,Double,NFloat,NDouble) where

import Prelude hiding (Float,Double)
import qualified Prelude as P

import Control.Arrow (first)

type Float  = NFloat
type Double = NDouble

-- "NFloat" and "NDouble" are to help track. Eliminate later.

newtype NFloat = F P.Float deriving (Eq,Ord,Num,Fractional,Floating)

instance Show NFloat where showsPrec p (F x) = showsPrec p x
instance Read NFloat where readsPrec p = (map . first) F . readsPrec p

newtype NDouble = D P.Double deriving (Eq,Ord,Num,Fractional,Floating)

instance Show NDouble where showsPrec p (D x) = showsPrec p x
instance Read NDouble where readsPrec p = (map . first) D . readsPrec p

