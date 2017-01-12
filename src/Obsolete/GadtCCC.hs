{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | GADT-based syntactic CCC

module ConCat.GadtCCC where

import Prelude hiding (id,(.))

import ConCat.Category
import ConCat.Misc ((:*),(:+),(:=>))
import ConCat.Rep (HasRep(..))

infix  0 :->

infixr 3 :&&&
infixr 2 :|||

-- | CCC combinator expressions.
data (:->) :: * -> * -> * where
  Id        :: a :-> a
  (:.)      :: (b :-> c) -> (a :-> b) -> (a :-> c)
  -- Products
  Exl       :: a :* b :-> a
  Exr       :: a :* b :-> b
  (:&&&)    :: (a :-> b) -> (a :-> c) -> (a :-> b :* c)
  It        :: a :-> ()
  -- Coproducts
  Inl       :: a :-> a :+ b
  Inr       :: b :-> a :+ b
  (:|||)    :: (b :-> a) -> (c :-> a) -> (b :+ c :-> a)
  DistL     :: a :* (b :+ c) :-> a :* b :+ a :* c
  -- Exponentials
  Apply     :: (a :=> b) :* a :-> b
  Curry     :: (a :* b :-> c) -> (a :-> (b :=> c))
  Uncurry   :: (a :-> (b :=> c)) -> (a :* b :-> c)
  -- Other
  Repr      :: a :-> Rep a
  Abst      :: Rep a :-> a
  Prim      :: String -> (a :-> b)
  Const     :: b -> (a :-> b)

instance Category (:->) where
  id = Id
  (.) = (:.)

instance ProductCat (:->) where
  exl = Exl
  exr = Exr
  (&&&) = (:&&&)

instance CoproductCat (:->) where
  inl = Inl
  inr = Inr
  (|||) = (:|||)

instance TerminalCat (:->) where it = It

instance DistribCat (:->) where distl = DistL

instance ClosedCat (:->) where
  apply = Apply
  curry = Curry
  uncurry = Uncurry

instance RepCat (:->) where
  reprC = Repr
  abstC = Abst

instance BoolCat (:->) where
  notC = Prim "notC"
  andC = Prim "andC"
  orC  = Prim "orC"
  xorC = Prim "xorC"

instance ConstCat (:->) b where
  const = Const
