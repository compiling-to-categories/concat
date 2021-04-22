{-# OPTIONS_GHC -Wall #-}

-- | Aliases for pointed functors, as the ones in Data.Pointed inline too early
module ConCat.Pointed (Pointed, point) where

import qualified Data.Pointed as Pointed
import Data.Pointed (Pointed)

point :: Pointed p => a -> p a
point = Pointed.point
{-# INLINE [0] point #-}
