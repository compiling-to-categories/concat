{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Indexed sets of morphisms

module ConCat.Nondet where

import Prelude hiding (id,(.),curry,uncurry,const)
import GHC.Types (Constraint)

import ConCat.Category

data ND k a b = forall p. Ok k p => ND (p -> (a `k` b))
  
exactly :: OkUnit k => (a `k` b) -> ND k a b
exactly f = ND (\ () -> f)

instance (Category k, OkProd k, OkUnit k) => Category (ND k) where
  type Ok (ND k) = Ok k
  id = exactly id
  -- ND g . ND f = ND (\ (p,q) -> g q . f p)
  ND (g :: q -> (b `k` c)) . ND (f :: p -> (a `k` b)) = ND (\ (p,q) -> g q . f p) <+ okProd @k @p @q

--   The constraint ‘OkProd k’ is no smaller than the instance head
--   (Use UndecidableInstances to permit this)

instance (ProductCat k, OkUnit k) => ProductCat (ND k) where
  exl = exactly exl
  exr = exactly exr 
  -- ND f &&& ND g = ND (\ (p,q) -> f p &&& g q)
  ND (f :: p -> (a `k` c)) &&& ND (g :: q -> (a `k` d)) = ND (\ (p,q) -> f p &&& g q) <+ okProd @k @p @q

instance (CoproductCat k, OkProd k, OkUnit k) => CoproductCat (ND k) where
  inl = exactly inl
  inr = exactly inr 
  -- ND f ||| ND g = ND (\ (p,q) -> f p ||| g q)
  ND (f :: p -> (a `k` c)) ||| ND (g :: q -> (b `k` c)) = ND (\ (p,q) -> f p ||| g q) <+ okProd @k @p @q

instance (DistribCat k, OkUnit k) => DistribCat (ND k) where
  distl = exactly distl
  distr = exactly distr 

instance (ClosedCat k, OkUnit k) => ClosedCat (ND k) where
  apply = exactly apply
  curry (ND f) = ND (curry . f)
  uncurry (ND g) = ND (uncurry . g)

instance (TerminalCat k, OkProd k, OkUnit k) => TerminalCat (ND k) where
  it = exactly it

instance (ConstCat k b, OkProd k, OkUnit k) => ConstCat (ND k) b where
  const b = exactly (const b)

instance (NumCat k a, ProductCat k, OkUnit k) => NumCat (ND k) a where
  addC    = exactly addC
  mulC    = exactly mulC
  negateC = exactly negateC
  powIC   = exactly powIC

-- Etc
