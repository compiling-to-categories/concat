{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experimenting with a replacement for Circuit

module ConCat.Graph where

import Prelude hiding (id,(.),curry,uncurry)

import Control.Arrow (Kleisli(..),arr)
import Control.Applicative (liftA2)
import Data.Sequence (Seq)

import Control.Newtype
-- mtl
import Control.Monad.State
import Control.Monad.Writer

import ConCat.Misc ((:*),(:=>),inNew,inNew2)
import ConCat.Category

-- Primitive operation, including literals
data Prim :: * -> * -> * where
  Literal :: b -> Prim () b
  Add :: Num a => Prim (a :* a) a
  -- ...

data Buses :: * -> * where
  UnitB    :: Buses ()
  -- BoolB    :: Source -> Buses Bool
  -- IntB     :: Source -> Buses Int
  -- FloatB   :: Source -> Buses Float
  -- DoubleB  :: Source -> Buses Double
  PairB    :: Buses a -> Buses b -> Buses (a :* b)
  -- ConvertB :: (T a, T b) => Buses a -> Buses b
  FunB     :: (e :* a :> b) -> Buses e -> Buses (a -> b)

-- Primitive or composed kernel
data Graph a b = PrimG (Prim a b) 
               | CompositeG (Buses a) (Buses b) Comps

type Comps = Seq (Exists2 Comp)

type CompNum = Int

-- Instantiated component with inputs and defining outputs
data Comp a b = Comp CompNum (Graph a b) (Buses a) (Buses b)

-- Existential wrapper
data Exists2 f = forall a b. Exists2 (f a b)

type GraphM = Writer Comps

infixl 1 :>, :+>

-- | Internal representation for '(:>)'.
type a :+> b = Kleisli GraphM (Buses a) (Buses b)

-- | Circuit category
newtype a :> b = C { unC :: a :+> b }

type BCirc a b = Buses a -> GraphM (Buses b)

pattern Circ :: BCirc a b -> (a :> b)
pattern Circ f = C (Kleisli f)

instance Newtype (a :> b) where
  type O (a :> b) = BCirc a b
  pack f = C (Kleisli f)
  unpack (C (Kleisli f)) = f

instance Category (:>) where
  id = C id
  C g . C f = C (g . f)

unPairB :: Ok2 (:>) a b => Buses (a :* b) -> Buses a :* Buses b
unPairB (PairB a b) = (a,b)

exlB :: Ok2 (:>) a b => Buses (a :* b) -> Buses a
exlB = exl . unPairB

exrB :: Ok2 (:>) a b => Buses (a :* b) -> Buses b
exrB = exr . unPairB

forkB :: BCirc a c -> BCirc a d -> BCirc a (c :* d)
forkB f g a = liftA2 PairB (f a) (g a)

instance ProductCat (:>) where
  exl = C (arr exlB)
  exr = C (arr exrB)
  (&&&) = inNew2 forkB
