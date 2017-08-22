{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Indexed sets of morphisms

module ConCat.Nondet where

import Prelude hiding (id,(.),curry,uncurry,const)
import GHC.Types (Constraint)

import ConCat.Category

type C p = (() :: Constraint)

data ND a b = forall p. C p => ND (p -> a -> b)  -- for some constraint C

exactly :: (a -> b) -> ND a b
exactly f = ND (\ () -> f)

instance Category ND where
  id = exactly id
  ND g . ND f = ND (\ (p,q) -> g q . f p)

instance ProductCat ND where
  exl = exactly exl
  exr = exactly exr 
  ND f &&& ND g = ND (\ (p,q) -> f p &&& g q)

instance CoproductCat ND where
  inl = exactly inl
  inr = exactly inr 
  ND f ||| ND g = ND (\ (p,q) -> f p ||| g q)

instance DistribCat ND where
  distl = exactly distl
  distr = exactly distr 

instance ClosedCat ND where
  apply = exactly apply
  curry (ND f) = ND (curry . f)
  uncurry (ND g) = ND (uncurry . g)

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
