{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
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

data ND k a b = forall p. C p => ND (p -> (a `k` b))  -- for some constraint C

exactly :: (a `k` b) -> ND k a b
exactly f = ND (\ () -> f)

instance Category k => Category (ND k) where
  type Ok (ND k) = Ok k
  id = exactly id
  ND g . ND f = ND (\ (p,q) -> g q . f p)

instance ProductCat k => ProductCat (ND k) where
  exl = exactly exl
  exr = exactly exr 
  ND f &&& ND g = ND (\ (p,q) -> f p &&& g q)

instance CoproductCat k => CoproductCat (ND k) where
  inl = exactly inl
  inr = exactly inr 
  ND f ||| ND g = ND (\ (p,q) -> f p ||| g q)

instance DistribCat k => DistribCat (ND k) where
  distl = exactly distl
  distr = exactly distr 

instance ClosedCat k => ClosedCat (ND k) where
  apply = exactly apply
  curry (ND f) = ND (curry . f)
  uncurry (ND g) = ND (uncurry . g)

instance TerminalCat k => TerminalCat (ND k) where
  it = exactly it

instance ConstCat k b => ConstCat (ND k) b where
  const b = exactly (const b)

instance (NumCat k a, ProductCat k) => NumCat (ND k) a where
  addC    = exactly addC
  mulC    = exactly mulC
  negateC = exactly negateC
  powIC   = exactly powIC

-- Etc
