{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experiments with derivative towers

module ConCat.Tower where

import Prelude hiding (id,(.),curry,uncurry,const)

import Control.Newtype (Newtype(..))

import ConCat.Misc ((:*))
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow

-- b :* (a :-* b) :* (a :-* a :-* b) :* ...
type T' s a b = b :* T s a b

-- (a :-* b) :* (a :-* a :-* b) :* ...
newtype T s a b = T (T' s a (L s a b))

newtype D s a b = D (a -> T' s a b)

instance Newtype (T s a b) where
  type O (T s a b) = T' s a (L s a b)
  pack h = T h
  unpack (T h) = h

instance Newtype (D s a b) where
  type O (D s a b) = a -> T' s a b
  pack h = D h
  unpack (D h) = h

zeroT :: (Num s, Zeroable (V s a), Zeroable (V s b)) => T s a b
zeroT = constT zeroLM
-- zeroT = T (zeroLM,zeroT)

constT :: (Num s, Zeroable (V s a), Zeroable (V s b)) => L s a b -> T s a b
constT f = T (f,zeroT)
{-# INLINE constT #-}

-- Differentiable linear function
linearD :: (Num s, HasV s a, HasV s b, HasL (V s a), HasL (V s b)) => L s a b -> D s a b
linearD f = D (\ a -> (lapply f a, constT f))
{-# INLINE linearD #-}

-- a :: a
-- f :: L s a b
-- lapply f a :: b
-- constT f :: T s a b

class    (Num s, HasV s a, HasL (V s a)) => OkT s a
instance (Num s, HasV s a, HasL (V s a)) => OkT s a

instance Category (T s) where
  type Ok (T s) = OkT s
  id = constT id
  T (g,g') . T (f,f') = T (g . f, _)


#if 0

T (g,g') :: T s b c
T (f,f') :: T s a b

g :: b :-* c
f :: a :-* b

g' :: T s b (b :-* c)
f' :: T s a (a :-* b)


-- (    let (b,f') = f a
--         (c,g') = g b
--     in
--       (c, g' . f'))

--   T g . T f = T (second (uncurry (.)) . rassocP . first g . f)

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

#endif

#if 0

-- newtype T' a b = T' (a :-* b :* (T' a b))

newtype P a b = P (a -> b :* Q a b)

newtype Q a b = Q b (Q a (a :-* b))

type Q a b = b :* Q a (a :-* b)

type Q a b = b :* (a :-* Q a b)


deriv' :: T a b -> T a (a -> b)

#endif
