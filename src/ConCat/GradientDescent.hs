{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.GradientDescent where

import Data.List (unfoldr)

import GHC.Generics (Par1(..))

import Control.Newtype (unpack)
import Data.Key (Zip)

import ConCat.Misc (Unop,Binop,R)
import ConCat.AD
import ConCat.Free.VectorSpace (HasV(..),onV,onV2)
import qualified ConCat.Free.VectorSpace as V
import ConCat.Free.LinearRow
import ConCat.Orphans ()
import ConCat.Category (dup)

gradientDescent :: forall a. (HasV R a, Zip (V R a))
                => R -> (a -> R) -> a -> [a]
gradientDescent epsilon f = unfoldr (Just . dup . next)
 where
   f' = gradient f
   next a = a ^-^ epsilon *^ f' a

gd1 :: [R]
gd1 = gradientDescent 0.1 (\ x -> x^2) 0.5

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- The vector operations in VectorSpace are on free vector spaces, so define
-- counterparts on regular values.

infixl 7 *^
infixl 6 ^-^

(*^) :: (HasV R a, Functor (V R a)) => R -> Unop a
(*^) s = onV ((V.*^) s)

(^-^) :: forall a. (HasV R a, Zip (V R a)) => Binop a
(^-^) = onV2 ((V.^-^) :: Binop (V R a R))

-- The specialization to R helps with type checking. Generalize if needed.

