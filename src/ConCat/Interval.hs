{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE IncoherentInstances #-}   -- ???

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Interval analysis

module ConCat.Interval where

import Prelude hiding (id,(.),curry,uncurry,const)

import Control.Newtype

import ConCat.Misc ((:*),(:+),R,inNew,inNew2)
import ConCat.Category

type family Iv a

type instance Iv ()  = ()
type instance Iv R   = R   :* R
type instance Iv Int = Int :* Int

data IF a b = IF { unIF :: Iv a -> Iv b }

instance Newtype (IF a b) where
  type O (IF a b) = Iv a -> Iv b
  pack = IF
  unpack = unIF

instance Category IF where
  id = pack id
  -- IF g . IF f = IF (g . f)
  (.) = inNew2 (.)

{-
    • Overlapping instances for Yes1 (Iv a) arising from a use of ‘id’
      Matching instances:
        instance forall k (a :: k). Yes1 a
          -- Defined at /Users/conal/Haskell/concat/src/ConCat/Misc.hs:98:10
      There exists a (perhaps superclass) match:
        from the context: Ok IF a
          bound by the type signature for:
                     id :: Ok IF a => IF a a
          at /Users/conal/Haskell/concat/src/ConCat/Interval.hs:30:3-4
      (The choice depends on the instantiation of ‘a’
       To pick the first instance above, use IncoherentInstances
       when compiling the other instance declarations)
-}

type instance Iv (a :* b) = Iv a :* Iv b

instance ProductCat IF where
  exl = pack exl
  exr = pack exr
  -- IF f &&& IF g = IF (f &&& g)
  (&&&) = inNew2 (&&&)

type instance Iv (a :+ b) = Iv a :+ Iv b

instance CoproductCat IF where
  inl = pack inl
  inr = pack inr
  (|||) = inNew2 (|||)

instance DistribCat IF where
  distl = pack distl
  distr = pack distr

type instance Iv (a -> b) = Iv a -> Iv b

instance ClosedCat IF where
  apply = pack apply
  -- curry (IF f) = IF (curry f)
  -- uncurry (IF g) = IF (uncurry g)
  curry = inNew curry
  uncurry = inNew uncurry

instance Iv b ~ (b :* b) => ConstCat IF b where
    const b = IF (const (b,b))
    unitArrow b = IF (unitArrow (b,b))

-- instance RepCat (->) a r => RepCat IF a r where

instance (Iv a ~ (a :* a), Num a, Ord a) => NumCat IF a where
  negateC = pack (\ (al,ah) -> (-ah, -al))
  addC = pack (\ ((al,ah),(bl,bh)) -> (al+bl,ah+bh))
  subC = addC . second negateC
  mulC = pack (\ ((al,ah),(bl,bh)) ->
               let cs = ((al*bl,al*bh),(ah*bl,ah*bh)) in
                 (min4 cs, max4 cs))
  powIC = error "powIC: not yet defined on IF"

min4,max4 :: Ord a => ((a :* a) :* (a :* a)) -> a
min4 ((a,b),(c,d)) = min (min a b) (min c d)
max4 ((a,b),(c,d)) = max (max a b) (max c d)
