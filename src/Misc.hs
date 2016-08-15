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

inNew :: (Newtype n, Newtype n') =>
         (O n -> O n') -> (n -> n')
inNew = pack <~ unpack

inNew2 :: (Newtype n, Newtype n', Newtype n'') =>
          (O n -> O n' -> O n'') -> (n -> n' -> n'')
inNew2 = inNew <~ unpack
