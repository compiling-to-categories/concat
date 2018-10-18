{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Experiment in nondeterministic functions as functions to lists.

-- Not much depends on lists. Could be any monad. General Kleisli?
-- Oh. I already have these instances defined for Kleisli in ConCat.Category.

module ConCat.Nondet where

import Prelude hiding (id,(.),curry,uncurry,const)
import GHC.Types (Constraint)

import Control.Applicative (liftA2)
import Control.Monad ((<=<))

import ConCat.Misc ((:+))
import ConCat.Category

newtype ND a b = ND (a -> [b])

exactly :: (a -> b) -> ND a b
exactly f = ND (pure . f)

instance Category ND where
  id = exactly id
  ND g . ND f = ND (g <=< f)

instance AssociativePCat ND where
  lassocP = exactly lassocP
  rassocP = exactly rassocP

instance BraidedPCat ND where swapP = exactly swapP

instance MonoidalPCat ND where
  ND f *** ND g = ND (\ (a,b) -> liftA2 (,) (f a) (g b))
  -- TODO: consider optimized first & second

instance ProductCat ND where
  exl = exactly exl
  exr = exactly exr 
  dup = exactly dup

-- Note that the universal product property holds only up to *set* equality of
-- lists, i.e., when the lists denote sets.

instance AssociativeSCat ND where
  lassocS = exactly lassocS
  rassocS = exactly rassocS

instance BraidedSCat ND where swapS = exactly swapS

instance MonoidalSCat ND where
  ND f +++ ND g = ND (map Left . f ||| map Right . g)
  -- TODO: consider optimized left & right

-- f :: a -> [c]
-- map Left  . f :: a -> [c :+ d]

-- g :: b -> [d]
-- map Right . g :: b -> [c :+ d]

instance CoproductCat ND where
  inl = exactly inl
  inr = exactly inr
  jam = exactly jam

instance DistribCat ND where
  distl = exactly distl
  distr = exactly distr 

#if 0

instance ClosedCat ND where
  apply = exactly apply
  curry (ND f) = ND (...)
  uncurry (ND g) = ND (...)

#endif

instance TerminalCat ND where
  it = exactly it

instance ConstCat ND b where
  const b = exactly (const b)

instance Num a => NumCat ND a where
  addC    = exactly addC
  mulC    = exactly mulC
  negateC = exactly negateC
  powIC   = exactly powIC

-- Etc
