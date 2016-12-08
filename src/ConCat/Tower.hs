{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.Tower where

import Prelude hiding (id,(.),curry,uncurry,const)

import Control.Newtype (Newtype(..))

import ConCat.Misc ((:*))
import qualified ConCat.Category as C
import ConCat.AltCat

newtype T a b = T (a -> b :* T a b)

instance Newtype (T a b) where
  type O (T a b) = a -> b :* T a b
  pack h = T h
  unpack (T h) = h

-- Differentiable linear function
linearT :: (a -> b) -> T a b
linearT f = t where t = T (f &&& const t)
{-# INLINE linearT #-}

instance Category T where
  id = linearT id

  T g . T f = T (\ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f'))

--   T g . T f = T (second (uncurry (.)) . rassocP . (first g . f))

instance ProductCat T where
  exl = linearT exl
  exr = linearT exr

  T f &&& T g = T (\ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g'))

--   T f &&& T g = T (second (uncurry (&&&)) . transposeP . (f &&& g))

fun :: T a b -> (a -> b)
-- fun (T h) = exl . h
-- fun = (exl .) . unpack
fun = (fmap.fmap) exl unpack

deriv :: T a b -> a -> T a b
-- deriv (T h) = exr . h
deriv = (fmap.fmap) exr unpack



-- newtype T' a b = T' (a :-* b :* (T' a b))

newtype P a b = P (a -> b :* Q a b)

newtype Q a b = Q b (Q a (a :-* b))

type Q a b = b :* Q a (a :-* b)

type Q a b = b :* (a :-* Q a b)


deriv' :: T a b -> T a (a -> b)
