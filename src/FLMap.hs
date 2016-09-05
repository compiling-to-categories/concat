{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Linear maps as wrapped functions

module FLMap where

import Prelude hiding (id,(.),curry,uncurry)

import Control.Newtype (Newtype(..))
import Data.Constraint (Dict(..),(:-)(..))

import Misc
import Additive
import Semimodule
import ConCat

class    Mod s u => OkL s u
instance Mod s u => OkL s u

type OkL2 s a b = (OkL s a, OkL s b)
type OkL3 s a b c = (OkL2 s a b, OkL s c)

data LMap s u v = LMap { unLMap :: u -> v }

instance OkL2 s u v => Newtype (LMap s u v) where
  type O (LMap s u v) = u -> v
  pack = LMap
  unpack = unLMap

-- | Function (assumed linear) as linear map.
linear :: OkL2 s u v => (u -> v) -> LMap s u v
linear = pack

-- | Apply a linear map to a vector.
lapply :: OkL2 s u v => LMap s u v -> (u -> v)
lapply = unpack

($@) :: OkL2 s a b => LMap s a b -> a -> b
($@) = lapply

instance OkL2 s u v => Semimodule (LMap s u v) where
  type Scalar (LMap s u v) = s
  (*^) s = inNew ((*^) s)

instance OkL2 s u v => Additive (LMap s u v) where
  zero = pack zero
  (^+^) = inNew2 (^+^)

instance Category (LMap s) where
  type Ok (LMap s) = OkL s
  id = linear id
  (.) = inNew2 (.)

instance OpCon (:*) (OkL s) where
  inOp = Sub Dict

instance ProductCat (LMap s) where
  type Prod (LMap s) = (:*)
  exl = linear exl
  exr = linear exr
  (&&&) = inNew2 (&&&)

instance CoproductCat (LMap s) where
  type Coprod (LMap s) = (:*)  -- direct sum
  inl = linear (, zero)
  inr = linear (zero ,)
  f ||| g = linear (lapply f `joinF` lapply g)

joinF :: Additive c => (a -> c) -> (b -> c) -> (a :* b -> c)
(f `joinF` g) (a,b) = f a ^+^ g b

applyTo :: OkL2 s a b => a -> LMap s (a -> b) b
applyTo a = linear ($ a)

packL :: (Newtype t, OkL2 s (O t) t) => LMap s (O t) t
packL = linear pack

unpackL :: (Newtype t, OkL2 s t (O t)) => LMap s t (O t)
unpackL = linear unpack
