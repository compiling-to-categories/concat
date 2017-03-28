{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Very simple image algebra, as in Pan

module ConCat.Image where

import Control.Applicative (liftA2)

import Data.NumInstances ()

import ConCat.Misc ((:*),R,Unop,Binop,sqr,magSqr)
-- import ConCat.AltCat (recipC)

type R2 = R :* R

{--------------------------------------------------------------------
    Spatial transformations
--------------------------------------------------------------------}

type Angle = R -- in radians

type Transform = Unop R2

rotateP :: Angle -> Transform
rotateP theta = \ (x,y) -> (x * c - y * s, y * c + x * s)
 where c = cos theta
       s = sin theta

translateP, scaleP :: R2 -> Transform
translateP = (+)
scaleP     = (*)

-- translateP (dx,dy) = \ (x,y) -> (x + dx, y + dy)
-- scaleP     (sx,sy) = \ (x,y) -> (sx * x, sy * y)

uniform :: (R2 -> a) -> (R -> a)
uniform f z = f (z,z)

uscaleP :: R -> Transform
uscaleP = uniform scaleP

{--------------------------------------------------------------------
    Images
--------------------------------------------------------------------}

type Image c = R2 -> c

type Region = Image Bool

type Filter c = Unop (Image c)

translate :: R2 -> Filter c
translate v im = im . subtract v

scale :: R2 -> Filter c
scale v im = im . (/ v)
-- scale v = (. scaleP (recip v))

uscale :: R -> Filter c
uscale = uniform scale

rotate :: R -> Filter c
rotate theta = (. rotateP (-theta))

complementR                     :: Applicative f => Unop  (f Bool)
intersectR, unionR, xorR, diffR :: Applicative f => Binop (f Bool)

complementR = fmap not
intersectR  = liftA2 (&&)
unionR      = liftA2 (||)
xorR        = liftA2 (/=)

r `diffR` r' = r `intersectR` complementR r'

-- | Half plane
xPos :: Region
xPos (x,_y) =  x > 0

-- | unit disk
udisk :: Region
udisk p = magSqr p <= 1

-- | disk
disk :: R -> Region
-- disk r = uscale r udisk
disk r = uniform scale r udisk

-- Alternative definition
disk' :: R -> Region
disk' r p = magSqr p <= sqr r

-- | Annulus, given outer & inner radii
annulus :: R -> R -> Region
annulus o i = disk o `diffR` disk i

-- | Checker-board
checker :: Region
checker (x,y) = test x == test y
  where test w = frac w > 0.5
{-# INLINE checker #-}
  
frac :: RealFrac a => a -> a
frac x = x - fromIntegral (floor x :: Int)
