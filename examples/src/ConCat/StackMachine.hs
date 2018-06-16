{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Stack machine category / compiler 

module ConCat.StackMachine where

import Prelude hiding (id,(.),curry,uncurry)

import Data.List (intercalate)

import Control.Newtype.Generics (Newtype(..))

import ConCat.Misc ((:*),(:+))
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Syntactic (Syn)

{--------------------------------------------------------------------
    Stack machines
--------------------------------------------------------------------}

newtype SM k a b = SM { unSM :: forall z. Ok k z => (a :* z) `k` (b :* z) }

-- | The semantic functor that specifies 'SM'.
pureSM :: (MonoidalPCat k, Ok2 k a b) => (a `k` b) -> SM k a b
pureSM f = SM (first f)

evalSM :: forall k a b. (Category k, UnitCat k, OkProd k, Ok2 k a b)
       => SM k a b -> (a `k` b)
evalSM (SM f) = rcounit . f . runit
                <+ okProd @k @a @()
                <+ okProd @k @b @()

-- TODO: Specify and derive the following instances by saying that pureSM is a
-- homomorphism for the classes involved.

instance MonoidalPCat k => Category (SM k) where
  type Ok (SM k) = Ok k
  id = pureSM id
  -- SM g . SM f = SM (g . f)
  (.) :: forall a b c. Ok3 k a b c => SM k b c -> SM k a b -> SM k a c
  SM g . SM f = SM h
   where
     h :: forall z. Ok k z => (a :* z) `k` (c :* z)
     h = g . f
       <+ okProd @k @a @z
       <+ okProd @k @b @z
       <+ okProd @k @c @z

instance BraidedPCat k => MonoidalPCat (SM k) where
  first :: forall a b c. Ok3 k a b c => SM k a c -> SM k (a :* b) (c :* b)
  first (SM f) = SM h
   where
     h :: forall z. Ok k z => ((a :* b) :* z) `k` ((c :* b) :* z)
     h = inRassocP f <+ okProd @k @b @z   -- h = lassocP . f . rassocP
  second = secondFirst  -- relies on BraidedPCat
  (***) = crossSecondFirst  -- f *** g = swap . first g . swap . first f
  lassocP :: forall a b c. Ok3 k a b c => SM k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = pureSM lassocP
            <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
            <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => SM k ((a :* b) :* c) (a :* (b :* c))
  rassocP = pureSM rassocP
            <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
            <+ okProd @k @(a :* b) @c <+ okProd @k @a @b

#if 0

f :: a -> b
g :: c -> d

rassocP    :: ((a :* b) :* z) -> (a :* (b :* z))
first f    :: (a :* (b :* z)) -> (c :* (b :* z))
lassocP    :: (c :* (b :* z)) -> ((c :* b) :* z)
first swap :: ((c :* b) :* z) -> (b :* (c :* z))
first g    :: (b :* (c :* z)) -> (d :* (c :* z))
rassocP    :: (d :* (c :* z)) -> ((d :* c) :* z)
first swap :: ((d :* c) :* z) -> ((c :* d) :* z)

#endif

instance BraidedPCat k => BraidedPCat (SM k) where
  swapP :: forall a b. Ok2 k a b => SM k (a :* b) (b :* a)
  swapP = pureSM swapP
        <+ okProd @k @a @b
        <+ okProd @k @b @a

instance ProductCat k => ProductCat (SM k) where
  exl :: forall a b. Ok2 k a b => SM k (a :* b) a
  exr :: forall a b. Ok2 k a b => SM k (a :* b) b
  dup :: forall a  . Ok  k a   => SM k a (a :* a)
  exl = pureSM exl <+ okProd @k @a @b
  exr = pureSM exr <+ okProd @k @a @b
  dup = pureSM dup <+ okProd @k @a @a

instance (MonoidalPCat k, TerminalCat k) => TerminalCat (SM k) where
  it = pureSM it

instance (ProductCat k, TerminalCat k, OkUnit k) => UnitCat (SM k)

-- instance (MonoidalPCat k, UnitCat k) => UnitCat (SM k) where
--   lunit :: forall a. Ok k a => SM k a (() :* a)
--   lunit = pureSM lunit <+ okProd @k @() @a
--   runit :: forall a. Ok k a => SM k a (a :* ())
--   runit = pureSM runit <+ okProd @k @a @()
--   lcounit :: forall a. Ok k a => SM k (() :* a) a
--   lcounit = pureSM lcounit <+ okProd @k @() @a
--   rcounit :: forall a. Ok k a => SM k (a :* ()) a
--   rcounit = pureSM rcounit <+ okProd @k @a @()

instance DistribCat k => MonoidalSCat (SM k) where
  -- SM f +++ SM g = SM (indistr (f +++ g))
  (+++) :: forall a b c d. Ok4 k a b c d => SM k a c -> SM k b d -> SM k (a :+ b) (c :+ d)
  SM f +++ SM g = SM h
   where
     h :: forall z. Ok k z => ((a :+ b) :* z) `k` ((c :+ d) :* z)
     h = indistr (f +++ g)
         <+ okProd @k @a @z <+ okProd @k @b @z
         <+ okProd @k @c @z <+ okProd @k @d @z

-- The validity of this (+++) definition relies on the following fact:
-- 
--   first (f +++ g) = indistr (first f +++ first g)
-- 
-- See proof in 2018-06-11 notes.

instance (BraidedSCat k, DistribCat k) => BraidedSCat (SM k) where
  swapS :: forall a b. Ok2 k a b => SM k (a :+ b) (b :+ a)
  swapS = pureSM swapS
        <+ okCoprod @k @a @b
        <+ okCoprod @k @b @a

instance DistribCat k => CoproductCat (SM k) where
  inl :: forall a b. Ok2 k a b => SM k a (a :+ b)
  inr :: forall a b. Ok2 k a b => SM k b (a :+ b)
  jam :: forall a. Ok k a => SM k (a :+ a) a
  inl = pureSM inl <+ okCoprod @k @a @b
  inr = pureSM inr <+ okCoprod @k @a @b
  jam = pureSM jam <+ okCoprod @k @a @a

instance (MonoidalPCat k, NumCat k a) => NumCat (SM k) a where
  negateC :: Ok k a => SM k a a
  addC,subC,mulC :: Ok k a => SM k (a :* a) a
  powIC :: Ok2 k a Int => SM k (a :* Int) a
  negateC = pureSM negateC
  addC    = pureSM addC  <+ okProd @k @a @a
  subC    = pureSM subC  <+ okProd @k @a @a
  mulC    = pureSM mulC  <+ okProd @k @a @a
  powIC   = pureSM powIC <+ okProd @k @a @Int

-- To do: write a GHC type-checker plugin that automatically applies `okProd`
-- and `okCoprod` entailments. Probably wait until the spurious recompilation
-- issue is fixed and I'm on a current GHC.

#if 0

t1 :: forall k a. (ProductCat k, NumCat k a) => a `k` a
t1 = addC . dup
  <+ okProd @k @a @a

t2 :: (ProductCat k, UnitCat k, NumCat k Int) => Int `k` Int
t2 = evalSM t1

t3 :: Int -> Int
t3 = t2

t4 :: Int
t4 = t3 17

t5 :: Syn Int Int
t5 = t2

t6 :: Syn (Int,z) (Int,z)
t6 = unSM t1

t7 :: Syn (Int :* Int) (Int :* Int)
t7 = negateC *** negateC

t8 :: Syn (Int :* Int) (Int :* Int)
t8 = evalSM (negateC *** negateC)

t9 :: Syn ((Int :* Int) :* z) ((Int :* Int) :* z)
t9 = unSM (negateC *** negateC)

t10 :: Syn ((Int :* Int) :* z) (Int :* z)
t10 = unSM (addC . (negateC *** negateC))

t11 :: Syn (Int :* z) (Int :* z)
t11 = unSM (addC . (negateC *** negateC) . dup)

t12 :: Syn (Int :* z) (Int :* z)
t12 = unSM (addC . (negateC &&& negateC))

#endif

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

data Exists2 k = forall a b. Exists2 (a `k` b)

instance Show2 k => Show (Exists2 k) where show (Exists2 f) = show2 f
