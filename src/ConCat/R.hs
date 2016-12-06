{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# OPTIONS_GHC -Wall #-}

-- | Experiment with representation polymorphism

module ConCat.R where

import Prelude hiding (Num)

import GHC.Types
import GHC.Exts (Int(..),Int#)

class HasRep r a | a -> r where
  type Rep r a :: TYPE r
  repr :: a -> Rep r a
  abst :: Rep r a -> a

instance HasRep IntRep Int where
  type Rep IntRep Int = Int#
  abst n = I# n
  repr (I# n) = n

-- class HasRep a where
--   type RepRep a :: RuntimeRep
--   type Rep a :: TYPE (RepRep a)
--   repr :: a -> Rep a
--   abst :: Rep a -> a

--     • Type constructor ‘RepRep’ cannot be used here
--         (it is defined and used in the same recursive group)
--     • In the first argument of ‘TYPE’, namely ‘RepRep a’
--       In the kind ‘TYPE (RepRep a)’

-- Is there a way to use an associated type here?
