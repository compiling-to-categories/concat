{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

{-# OPTIONS_GHC -Wall #-}

-- | Miscellany

module Misc where

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

infixr 1 +->
data (a +-> b) p = Fun1 { unFun1 :: a p -> b p }

-- TODO: resolve name conflict with tries. Using ":->:" for functors fits with
-- other type constructors in GHC.Generics.

instance Newtype ((a +-> b) t) where
  type O ((a +-> b) t) = a t -> b t
  pack = Fun1
  unpack = unFun1


{--------------------------------------------------------------------
    Other
--------------------------------------------------------------------}

infixl 1 <~
infixr 1 ~>

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

