{-# LANGUAGE UndecidableInstances #-}
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

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

-- #define SpecialPair

----------------------------------------------------------------------
-- | Uniform pairs
----------------------------------------------------------------------

module ConCat.Pair
  (
#ifdef SpecialPair
    Pair(..)
#else
    Pair
#endif
  , pattern (:#)
  ) where

import GHC.Generics (Par1(..),(:*:)(..))
#ifdef SpecialPair
import GHC.Generics (Generic1(..))
#endif

#ifdef SpecialPair
import Control.Applicative (liftA2)
import Data.Key
import Data.Pointed
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(tabulate,index))
import qualified Data.Functor.Rep as R
import Control.Newtype (Newtype(..))
import Data.Constraint (Dict(..),(:-)(..))

import ConCat.Misc ((:*))
import ConCat.Rep (HasRep(..))
import ConCat.Sized
import ConCat.Scan
import ConCat.Circuit ((:>),GenBuses(..),Buses(..),BusesM,Ty(..),abstB)
import ConCat.Free.VectorSpace (HasV(..))
import ConCat.AltCat (type (|-)(..),Ok)
#endif

#ifndef SpecialPair

-- | Uniform pair
type Pair = Par1 :*: Par1

pattern (:#) :: a -> a -> Pair a
pattern x :# y = Par1 x :*: Par1 y

#else

type GPair = Par1 :*: Par1

newtype Pair a = Pair (GPair a)

instance Newtype (Pair a) where
  type O (Pair a) = GPair a
  pack as = Pair as
  unpack (Pair as) = as

instance Generic1 Pair where
  type Rep1 Pair = GPair
  to1 p = Pair p
  from1 (Pair p) = p

infixl 1 :#

pattern (:#) :: a -> a -> Pair a
pattern x :# y = Pair (Par1 x :*: Par1 y)

instance Show a => Show (Pair a) where
  showsPrec p = \ (x :# y) -> showParen (p >= 1) $ showsPrec 1 x . showString " :# " . showsPrec 1 y

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

instance Distributive Pair where
  distribute ps = pack (distribute (unpack <$> ps))

instance Representable Pair where
  type Rep Pair = R.Rep GPair
  tabulate f = Pair (tabulate f)
  index (Pair xs) = R.index xs

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

instance OkFunctor (:>) Pair where
  okFunctor = Entail (Sub Dict)

-- Without these NOINLINE pragmas, GHC's typechecker does exponential work for
-- binary trees.

instance LScan Pair

deriving instance Zip Pair

#endif
