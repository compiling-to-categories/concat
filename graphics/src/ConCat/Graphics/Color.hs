{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Graphics.Color
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
--
-- Simple colors
----------------------------------------------------------------------

module ConCat.Graphics.Color
  (
  -- * Basics
    Color, rgba, rgb, colorR, colorG, colorB, colorA
  -- * Color operations
  , overC, over
  -- * Some colors
  , black, white, red, green, blue, clear, grey, gray
  -- * Conversion to color
  , HasColor(..)
  ) where

import Data.Monoid (Monoid(..))
import Control.Applicative (liftA2)

import ConCat.Misc (R)

-- import Control.Compose ((~>))

-- import Data.VectorSpace

-- import Data.Boolean

import ConCat.Misc (Unop, Binop)

{--------------------------------------------------------------------
    Basics
--------------------------------------------------------------------}

-- | Color
data Color = Color R R R R

-- | Color from red, green, blue, alpha components
rgba :: R -> R -> R -> R -> Color
rgba = Color

-- | Color from red, green, blue components
rgb :: R -> R -> R -> Color
rgb r g b = rgba r g b 1

-- | Extract the red component
colorR :: Color -> R
colorR (Color r _ _ _) = r

-- | Extract the green component
colorG :: Color -> R
colorG (Color _ g _ _) = g

-- | Extract the blue component
colorB :: Color -> R
colorB (Color _ _ b _) = b

-- | Extract the alpha component
colorA :: Color -> R
colorA (Color _ _ _ a) = a

{--------------------------------------------------------------------
    Color operations
--------------------------------------------------------------------}

-- | Overlay on two colors
overC :: Binop Color
overC (Color tr tg tb ta) (Color br bg bb ba) =
  Color (f tr br) (f tg bg) (f tb bb) (f ta ba)
 where
   f top bot = top + (1 - ta) * bot

-- | Pointwise 'overC', e.g., for images.
over :: Binop (p -> Color)
over = liftA2 overC


{--------------------------------------------------------------------
    Some colors
--------------------------------------------------------------------}

-- | Some colors
black, white, red, green, blue, clear :: Color
black = grey 0
white = grey 1

red   = rgb 1 0 0
green = rgb 0 1 0
blue  = rgb 0 0 1

clear = rgba 0 0 0 0

-- | Shade of grey
grey, gray :: R -> Color
grey x = rgb x x x
gray = grey

instance Monoid Color where
  mempty  = clear
  mappend = overC

{--------------------------------------------------------------------
    Conversion to color
--------------------------------------------------------------------}

class HasColor a where toColor :: a -> Color

instance HasColor Color where toColor = id
instance HasColor Bool  where toColor b = if b then clear else white  -- or black & white
