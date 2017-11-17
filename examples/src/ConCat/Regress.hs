{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- -- Does this flag make any difference?
-- {-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- | Multi-dimensional regression
module ConCat.Regress where

import Data.Key (Zip(..))

import ConCat.Misc ((:*),Binop)
import ConCat.AltCat (Ok)
import qualified ConCat.Free.VectorSpace as V
import ConCat.Free.VectorSpace hiding ((^+^),distSqr)
import ConCat.Free.LinearRow
-- import ConCat.Free.Affine

-- There's not much here now. See ConCat.Free.Affine.

-- Square of distance between predicted and observed datum
sqErr :: Ok (L s) b => a :* b -> (a -> b) -> s
sqErr (x,y) h = h x `distSqr` y
{-# INLINE sqErr #-}

add :: forall s a. (HasV s a, Zip (V s a), Num s) => Binop a
add = onV2 @s (V.^+^)
{-# INLINE add #-}

-- | Distance squared
distSqr :: forall s a. (HasV s a, Zip (V s a), Foldable (V s a), Num s) => a -> a -> s
distSqr a b = V.distSqr (toV a) (toV b)
{-# INLINE distSqr #-}
