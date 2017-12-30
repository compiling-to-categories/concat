{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation

module ConCat.AD where

import Prelude hiding (id,(.),curry,uncurry,const,unzip)

import GHC.Generics(Par1(..))

import ConCat.Misc ((:*))
import ConCat.Rep (repr)
import ConCat.Free.VectorSpace (HasV(..),IsScalar)
import ConCat.Free.LinearRow
import ConCat.AltCat
import ConCat.GAD

-- | Differentiable functions with composed-functor style linear maps as
-- derivatives.
type D s = GD (L s)

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

andDer :: forall s a b . (a -> b) -> (a -> b :* L s a b)
andDer = andDeriv
{-# INLINE andDer #-}

der :: forall s a b . (a -> b) -> (a -> L s a b)
der = deriv
{-# INLINE der #-}

gradient :: (HasV s a, IsScalar s) => (a -> s) -> a -> a
gradient f = gradientD (toCcc f)
{-# INLINE gradient #-}

gradientD :: (HasV s a, IsScalar s) => D s a s -> a -> a
gradientD (D h) = unV . unPar1 . repr . snd . h
{-# INLINE gradientD #-}


--                             f :: a -> s
--                         der f :: a -> L s a s
--                unpack . der f :: a -> V s s (V s a s)
--                               :: a -> Par1 (V s a s)
--       unPar1 . unpack . der f :: a -> V s a s
-- unV . unPar1 . unpack . der f :: a -> a

