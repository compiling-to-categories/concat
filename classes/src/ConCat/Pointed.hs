{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Alternative to Data.Pointed. Temporay (I hope) workaround to a difficulty
-- the plugin sometimes has with single-method classes. See 2018-04-06 notes.

module ConCat.Pointed (Pointed(..),point) where

import Data.Proxy

import qualified Data.Pointed as P

class P.Pointed f => Pointed f where
  point' :: a -> f a
  point' = P.point
  {-# INLINE [0] point' #-}
  pointedDummy :: Proxy f
  pointedDummy = Proxy

instance P.Pointed f => Pointed f

point :: Pointed f => a -> f a
point = point'
{-# INLINE [0] point #-}
-- {-# NOINLINE point #-}

-- If & when I get this trick working, find the simplest variant.
-- Do I need two methods in Pointed, or do a superclass and one method suffice?
