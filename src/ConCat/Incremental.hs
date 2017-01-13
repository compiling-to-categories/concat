{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experimenting with incremental computation

module ConCat.Incremental where

import Prelude hiding (id,(.))
import Data.Maybe (fromMaybe)

import Data.Void (Void,absurd)
import Control.Newtype
import Data.Constraint ((:-)(..),Dict(..))

import ConCat.Misc ((:*),(:+),Unop,inNew2,Parity)
import ConCat.Rep
import qualified ConCat.Category
import ConCat.AltCat hiding (const,curry,uncurry)

-- For DelRep:
import ConCat.Complex
import Data.Monoid
import Control.Applicative (WrappedMonad(..))
import qualified GHC.Generics as G
import Data.Functor.Identity (Identity(..))
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Monad.Trans.State (StateT(..))

{--------------------------------------------------------------------
    Changes
--------------------------------------------------------------------}

-- Delta for "Atomic" (all-or-nothing) values.
-- Nothing for no change, and Just a for new value a.
type AtomDel a = Maybe a

type Atomic a = (HasDelta a, Delta a ~ AtomDel a)

class HasDelta a where
  type Delta a
  type Delta a = AtomDel a
  appD :: Delta a -> Unop a
  default appD :: Atomic a => Delta a -> Unop a
  appD del old = fromMaybe old del
  zeroD :: Delta a
  default zeroD :: Atomic a => Delta a
  zeroD = Nothing

-- Unit can't change.
instance HasDelta () where
  type Delta () = Maybe Void
  appD d () = maybe () absurd d
  zeroD = Nothing

-- instance HasDelta ()

instance HasDelta Bool
instance HasDelta Int
instance HasDelta Float
instance HasDelta Double

instance (HasDelta a, HasDelta b) => HasDelta (a :* b) where
  type Delta (a :* b) = Delta a :* Delta b
  appD (da,db) = appD da *** appD db
  zeroD = (zeroD @a, zeroD @b)

instance (HasDelta a, HasDelta b) => HasDelta (a :+ b) where
  -- No change, left, right
  type Delta (a :+ b) = Maybe (Delta a :+ Delta b)
  appD :: Maybe (Delta a :+ Delta b) -> Unop (a :+ b)
  appD Nothing           e = e
  appD (Just (Left  da)) (Left  a) = Left  (appD da a)
  appD (Just (Right da)) (Right a) = Right (appD da a)
  appD _ _ = error "appD: left/right mismatch"
  zeroD = Nothing

#define DelRep(ty) \
  instance (HasRep (ty), HasDelta (Rep (ty))) => HasDelta (ty)

DelRep((a,b,c))
DelRep((a,b,c,d))
DelRep((a,b,c,d,e))
DelRep((a,b,c,d,e,f))
DelRep((a,b,c,d,e,f,g))
DelRep((a,b,c,d,e,f,g,h))

DelRep(Complex a)
DelRep(Maybe a)
DelRep(Sum a)
DelRep(Product a)
DelRep(All)
DelRep(Any)
DelRep(Dual a)
DelRep(Endo a)
DelRep(WrappedMonad m a)
DelRep(Identity a)
DelRep(ReaderT e m a)
DelRep(WriterT w m a)
DelRep(StateT s m a)

DelRep(G.U1 p)
DelRep(G.Par1 p)
DelRep(G.K1 i c p)
DelRep(G.M1 i c f p)
DelRep((f G.:+: g) p)
DelRep((f G.:*: g) p)
DelRep((g G.:.: f) p)

DelRep(Parity)

--     • The constraint ‘HasRep t’ is no smaller than the instance head
--       (Use UndecidableInstances to permit this)

{--------------------------------------------------------------------
    Change transformations
--------------------------------------------------------------------}

infixr 1 -+>
newtype a -+> b = DelX { unDelX :: Delta a -> Delta b }

zeroDelX :: forall a b. HasDelta b => a -+> b
zeroDelX = DelX (const (zeroD @b))

instance Newtype (a -+> b) where
  type O (a -+> b) = Delta a -> Delta b
  pack f = DelX f
  unpack (DelX f) = f

type OkDelX = HasDelta

instance Category (-+>) where
  type Ok (-+>) = OkDelX
  id  = pack id
  (.) = inNew2 (.)

instance OpCon (:*) (Sat OkDelX) where inOp = Entail (Sub Dict)
instance OpCon (:+) (Sat OkDelX) where inOp = Entail (Sub Dict)

instance ProductCat (-+>) where
  exl   = pack exl
  exr   = pack exr
  (&&&) = inNew2 (&&&)

instance CoproductCat (-+>) where
  inl = pack (Just . Left )
  inr = pack (Just . Right)
  (|||) :: forall a b c. Ok3 (-+>) a b c => (a -+> c) -> (b -+> c) -> (a :+ b -+> c)
  DelX f ||| DelX g = DelX (maybe (zeroD @c) (f ||| g))

atomic1 :: (Atomic a, Atomic b) => (a -> b) -> a -> (a -+> b)
atomic1 f a = DelX $ \ case
  Nothing -> Nothing
  d       -> Just (f (appD d a))

atomic2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> a :* b -> (a :* b -+> c)
atomic2 f ab = DelX $ \ case
  (Nothing, Nothing) -> Nothing
  d                  -> Just (f (appD d ab))
