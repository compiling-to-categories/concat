{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

{-# OPTIONS_GHC -Wall #-}

-- | Miscellany

module Misc where

import GHC.Generics ((:+:)(..),(:*:)(..))
import Control.Newtype

{--------------------------------------------------------------------
    Type abbreviations
--------------------------------------------------------------------}

infixl 7 :*
infixl 6 :+
infixr 1 :=>

type Unit  = ()

type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

{--------------------------------------------------------------------
    Helpers for GHC.Generics
--------------------------------------------------------------------}

prodF :: a t :* b t -> (a :*: b) t
prodF = uncurry (:*:)

unProdF :: (a :*: b) t -> a t :* b t
unProdF (a :*: b) = (a,b)

eitherF :: (a t -> c) -> (b t -> c) -> ((a :+: b) t -> c)
eitherF f _ (L1 a) = f a
eitherF _ g (R1 b) = g b

sumF :: a t :+ b t -> (a :+: b) t
sumF = either L1 R1

unSumF :: (a :+: b) t -> a t :+ b t
unSumF = eitherF Left Right

infixr 1 +->
infixr 0 $*
data (a +-> b) p = Fun1 { ($*) :: a p -> b p }

-- TODO: resolve name conflict with tries. Using ":->:" for functors fits with
-- other type constructors in GHC.Generics.

{--------------------------------------------------------------------
    Other
--------------------------------------------------------------------}

-- | Add pre- and post-processing
(~>) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(~>) = flip (<~)

-- | Add post- and pre-processing
(<~) :: (b -> b') -> (a' -> a) -> ((a -> b) -> (a' -> b'))
(h <~ f) g = h . g . f


class    Yes a
instance Yes a

inNew :: (Newtype p, Newtype q) =>
         (O p -> O q) -> (p -> q)
inNew = pack <~ unpack

inNew2 :: (Newtype p, Newtype q, Newtype r) =>
          (O p -> O q -> O r) -> (p -> q -> r)
inNew2 = inNew <~ unpack

-- TODO: use inNew and inNew2 in place of ad hoc versions throughout.

