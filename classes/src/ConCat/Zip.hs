{-# OPTIONS_GHC -Wall #-}

-- | Aliases for zippable functors, as the ones in Key.Zip inline too early
module ConCat.Zip(Zip, zipWith, zip, zap) where

-- use with
-- import Prelude hiding (zipWith, zip)

import Prelude hiding (zipWith, zip)
import qualified Data.Key as Key
import Data.Key (Zip)

zipWith :: Zip f => (a -> b -> c) -> f a -> f b -> f c
zipWith = Key.zipWith
{-# INLINE [0] zipWith #-}

zip :: Zip f => f a -> f b -> f (a, b)
zip = Key.zip
{-# INLINE [0] zip #-}

zap :: Zip f => f (a -> b) -> f a -> f b 
zap = Key.zap
{-# INLINE [0] zap #-}
