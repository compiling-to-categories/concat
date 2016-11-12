{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}


{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | A value-based entailment category

module ConCat.Entail where

import Prelude hiding (id,(.),curry,uncurry)

import GHC.Types (Constraint)
import Data.Constraint hiding ((&&&),(***),(:=>))

import Control.Newtype

import ConCat.Category hiding (type (|-),(<+))
import ConCat.Misc ((:*),type (&&),inNew2)

class HasCon a where
  type Con a :: Constraint
  toD  :: a -> Dict (Con a)
  unD' :: Con a => a

unD :: HasCon a => Dict (Con a) -> a
unD Dict = unD'

instance HasCon (Dict c) where
  type Con (Dict c) = c
  toD  = id
  unD' = Dict

instance (HasCon a, HasCon b) => HasCon (a :* b) where
  type Con (a :* b) = Con a && Con b
  toD (toD -> Dict, toD -> Dict) = Dict
  unD' = (unD',unD')

infixr 1 |-
newtype a |- b = Entail (Con a :- Con b)

instance Newtype (a |- b) where
  type O (a |- b) = Con a :- Con b
  pack e = Entail e
  unpack (Entail e) = e

instance Category (|-) where
  -- type Ok (|-) = HasCon
  id = pack refl
  (.) = inNew2 (\ g  f -> Sub $ Dict \\ g \\ f)

instance OpCon (:*) HasCon where
  inOp = Sub Dict

instance ProductCat (|-) where
  type Prod (|-) = (:*)
  exl = pack (Sub Dict)
  exr = pack (Sub Dict)
  dup = pack (Sub Dict)
  (&&&) = inNew2 $ \ f g -> Sub $ Dict \\ f \\ g
  (***) = inNew2 $ \ f g -> Sub $ Dict \\ f \\ g

infixl 1 <+

-- | Wrapper
(<+) :: Con a => (Con b => r) -> (a |- b) -> r
f <+ Entail e = f \\ e

