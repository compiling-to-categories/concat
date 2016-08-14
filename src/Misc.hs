{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

{-# OPTIONS_GHC -Wall #-}

-- | Miscellany

module Misc where

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

class    Yes a
instance Yes a
