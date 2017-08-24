{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

#define SpecialPair

----------------------------------------------------------------------
-- | Uniform pairs
----------------------------------------------------------------------

module ConCat.Pair (Pair, pattern (:#)) where

import GHC.Generics (Par1(..),(:*:)(..))
#ifdef SpecialPair
import GHC.Generics (Generic1(..))
#endif

#ifdef SpecialPair
import Control.Applicative (liftA2)
import Data.Key
import Data.Pointed

import ConCat.Misc ((:*))
import ConCat.Rep (HasRep(..))
import ConCat.Sized
import ConCat.Scan
import ConCat.Circuit (GenBuses(..),Buses(..),BusesM,Ty(..),abstB)
import ConCat.Free.VectorSpace (HasV(..))
#endif

#ifndef SpecialPair

-- | Uniform pair
type Pair = Par1 :*: Par1

pattern (:#) :: a -> a -> Pair a
pattern x :# y = Par1 x :*: Par1 y

#else

type GPair = Par1 :*: Par1

newtype Pair a = Pair (GPair a)

instance Generic1 Pair where
  type Rep1 Pair = GPair
  to1 p = Pair p
  from1 (Pair p) = p

infixl 1 :#

pattern (:#) :: a -> a -> Pair a
pattern x :# y = Pair (Par1 x :*: Par1 y)

instance HasRep (Pair a) where
  type Rep (Pair a) = a :* a
  -- repr (a :# a') = (a,a')  -- *
  repr = \ (a :# a') -> (a,a')
  abst (a,a') = a :# a'

-- * GHC 8.0.2 objects to the first version of repr:
-- 
--     Pattern match(es) are non-exhaustive
--     In an equation for ‘repr’: Patterns not matched: _
--
-- TODO: try again with a later GHC.

deriving instance Functor Pair
deriving instance Applicative Pair
deriving instance Monad Pair
deriving instance Foldable Pair
deriving instance Traversable Pair

deriving instance Pointed Pair

instance HasV s a => HasV s (Pair a)

-- -- "Ambiguous type variable ‘f0’ arising from a use of ‘size’"
-- deriving instance Sized Pair

instance Sized Pair where size = 2

instance GenBuses a => GenBuses (Pair a) where
  genBuses' prim ins = abstB <$> (ProdB <$> gb <*> gb)
   where
     gb :: BusesM (Buses a)
     gb = genBuses' prim ins
     {-# NOINLINE gb #-}
  ty = Prod t t
   where
     t = ty @a
     {-# NOINLINE t #-}
  unflattenB' = ConvertB <$> liftA2 ProdB u u
   where
     u = unflattenB' @a
     {-# NOINLINE u #-}

-- Without these NOINLINE pragmas, GHC's typechecker does exponential work for
-- binary trees.

instance LScan Pair

deriving instance Zip Pair

#endif
