{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wall #-}

-- | Experiment with representation polymorphism

module ConCat.R where

import Prelude hiding (Num)

import GHC.Types
import GHC.Exts (Int(..),Int#)

type family RepRep a :: RuntimeRep

class HasRep a where
  type Rep a :: TYPE (RepRep a)
  repr :: a -> Rep a
  abst :: Rep a -> a

type instance RepRep Int = IntRep

instance HasRep Int where
  type Rep Int = Int#
  abst n = I# n
  repr (I# n) = n

--     • Expected kind ‘TYPE (RepRep Int)’,
--         but ‘Int#’ has kind ‘TYPE 'IntRep’
--     • In the type ‘Int#’
--       In the type instance declaration for ‘Rep’
--       In the instance declaration for ‘HasRep Int’
