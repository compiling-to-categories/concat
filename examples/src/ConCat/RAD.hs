{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Reverse mode AD

module ConCat.RAD (andDerR,derR,andGradR,gradR) where

import Prelude hiding (id,(.),const,unzip)

import Data.Constraint (Dict(..),(:-)(..))

import Data.Pointed
import Data.Key
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..))

import ConCat.Misc ((:*),Yes1,result,sqr,unzip,cond)
import ConCat.Category
import ConCat.AltCat (toCcc)
import qualified ConCat.AltCat as A
import qualified ConCat.Rep as R
import ConCat.AdditiveFun
-- import ConCat.DualAdditive
import ConCat.Dual
import ConCat.GAD

-- Differentiable functions
type RAD = GD (Dual (-+>))

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

-- | Add a dual/reverse derivative
andDerR :: forall a b. (a -> b) -> (a -> b :* (b -> a))
andDerR f = (result.second) R.repr (unMkD (toCcc f :: RAD a b))
{-# INLINE andDerR #-}

-- | Dual/reverse derivative
derR :: (a -> b) -> (a -> (b -> a))
derR = (result.result) snd andDerR
{-# INLINE derR #-}

andGradR :: Num s => (a -> s) -> (a -> s :* a)
andGradR = (result.result.second) ($ 1) andDerR
{-# INLINE andGradR #-}

gradR :: Num s => (a -> s) -> (a -> a)
gradR = (result.result) snd andGradR
{-# INLINE gradR #-}
