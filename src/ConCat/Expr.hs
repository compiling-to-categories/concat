{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}

-- TODO: trim extensions


{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | First-order, monomorphic expression language with explicit sharing

module ConCat.Expr where

import Prelude hiding (id,(.))

import Control.Newtype (Newtype(..))

import ConCat.Misc ((:*),inNew,inNew2)
import ConCat.Category

data Prim :: * -> * -> * where 
  NegateP :: Num a => Prim a a
  AddP, SubP, MulP :: Num a => Prim (a :* a) a
  ExlP :: Prim (a :* b) a
  ExrP :: Prim (a :* b) b

#if 0

data E :: * -> * -> * where
  Lit :: a -> E env a
  App :: Prim a b -> E env a  -> E env b
  Let :: E env a -> E (a :* env) b -> E env b
  Env :: E env env
  Unit :: E env ()
  Pair :: E env a -> E env b -> E env (a :* b)

#endif

{--------------------------------------------------------------------
    HOAS
--------------------------------------------------------------------}

data E :: * -> * where
  Lit :: a -> E a
  App :: Prim a b -> E a -> E b
  Let :: E a -> (E a -> E b) -> E b
  Unit :: E ()
  Pair :: E a -> E b -> E (a :* b)
  -- Lam :: (E a -> E b) -> E (a -> b)  -- for Closed

newtype EFun a b = EFun (E a -> E b)

instance Newtype (EFun a b) where
  type O (EFun a b) = E a -> E b
  pack f = EFun f
  unpack (EFun f) = f

instance Category EFun where
  id = pack id
  (.) = inNew2 (.)

dupP :: E a -> E (a :* a)
dupP e = Let e (\ x -> Pair x x)

exlP :: E (a :* b) -> E a
exlP = App ExlP

exrP :: E (a :* b) -> E b
exrP = App ExrP

instance ProductCat EFun where
  exl = pack exlP
  exr = pack exrP
  (&&&) = inNew2 (\ f g -> \ x -> Let x (\ y -> Pair (f y) (g y)))
  (***) = inNew2 (\ f g ->
    \ case Pair a b -> Pair (f a) (g b)
           e -> Let e (\ y -> Pair (f (exlP y)) (g (exrP y))))

#if 0

instance ClosedCat EFun where
  apply = pack (\ (Pair (Lam f) a) -> f a)  -- safe?
  curry = inNew (...)

-- EFun (a :* b) -> E c
-- =~ E (a :* b) -> E c
-- =~ E a :* E b -> E c
-- =~ E a -> (E b -> E c)
-- =~ E a -> (E b -> E c)

#endif
