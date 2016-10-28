{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns, TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification, TypeSynonymInstances, GADTs #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-} -- for LU & BU
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
{-# LANGUAGE TypeApplications, AllowAmbiguousTypes #-}

-- TODO: trim LANGUAGE pragmas

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Reworked from Circat.Circuit

module Graph where

import Control.Arrow (Kleisli(..))
import Data.Typeable

import Control.Monad.State (State,StateT,execState,evalStateT,modify)

import Misc ((:*))
import ConCat

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

data Exists f = forall a. Exists (f a)

data Ty a = Typeable a => Ty { }

type ETy = Exists Ty

{--------------------------------------------------------------------
    Pins & buses
--------------------------------------------------------------------}

newtype PinId = PinId Int deriving (Eq,Ord,Show,Enum)
type PinSupply = [PinId]

-- Data bus: Id and type
data Bus a = Bus PinId (Ty a)

-- type family Buses a :: *
type family Buses a = r | r -> a

type instance Buses ()     = Bus ()
type instance Buses Bool   = Bus Bool
type instance Buses Int    = Bus Int
type instance Buses Float  = Bus Float
type instance Buses Double = Bus Double

type instance Buses (a :* b) = Buses a :* Buses b
type instance Buses (a -> b) = a :> b

data Source a = Source (Bus a) PrimName Sources Int

type ESource = Exists Source

type Sources = [ESource]

flattenB :: String -> Buses a -> Sources
flattenB = undefined

-- flattenB name b = fromMaybe err (flattenMb b)
--  where
--    err = error $ "flattenB/"++name++": unhandled " ++ show b

-- flattenMb :: Buses a -> Maybe Sources
-- flattenMb = fmap toList . flat
--  where
--    flat :: Buses a -> Maybe (Seq Source)
--    flat UnitB       = Just mempty
--    flat (BoolB b)   = Just (singleton' b)
--    flat (IntB b)    = Just (singleton' b)
--    flat (FloatB  b) = Just (singleton' b)
--    flat (DoubleB b) = Just (singleton' b)
--    flat (PairB a b) = liftA2 (<>) (flat a) (flat b)
--    flat (IsoB b)    = flat b
--    flat (FunB _)    = Nothing
--    singleton' = singleton . Exists

{--------------------------------------------------------------------
    Circuit monad
--------------------------------------------------------------------}

type PrimName = String

-- | Primitive of type @a -> b@
data Prim a b = (Typeable a, Typeable b) => Prim { primName :: PrimName }

-- Component: primitive instance with inputs & outputs
data Comp = forall a b. Comp (Prim a b) (Buses a) (Buses b)

type CompInfo = [Comp]

type CircuitM = State (PinSupply,CompInfo)

type BCirc a b = Buses a -> CircuitM (Buses b)

genBuses :: GenBuses b => Prim a b -> Sources -> CircuitM (Buses b)
genBuses prim ins = evalStateT (genBuses' (primName prim) ins) 0

type BusesM = StateT Int CircuitM

class GenBuses a where
  genBuses' :: String -> Sources -> BusesM (Buses a)
--   delay :: a -> (a :> a)
--   ty :: a -> Ty                         -- dummy argument

-- Instantiate a 'Prim'
genComp :: forall a b. GenBuses b => Prim a b -> BCirc a b
genComp prim a = do b <- genBuses prim (flattenB "genComp" a)
                    modify (second (Comp prim a b :))
                    return b

{--------------------------------------------------------------------
    Category
--------------------------------------------------------------------}

infixl 1 :>

type (:>) = Kleisli CircuitM

-- instance BoolCat (:>) where
--   type BoolOf (:>) = Source Bool
--   notC = pack 
