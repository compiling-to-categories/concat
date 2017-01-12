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
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experimenting with incremental computation

module ConCat.Incremental where

import Prelude hiding (id,(.))
import qualified Prelude as P
import Data.Monoid (Any(..))
import Control.Applicative (liftA2)
import Control.Arrow (Kleisli)
import Data.Maybe (fromMaybe)

import Data.Void
import Data.Constraint ((:-)(..),Dict(..))
import Control.Newtype

import ConCat.Misc ((:*),(:+),Unop,Binop,inNew,inNew2,Yes1)
import qualified ConCat.Category
import ConCat.AltCat hiding (const,curry,uncurry)

#if 0

data Delta :: * -> * where
  ConstD :: a -> Delta a
  IdD    :: Delta a
  (:***) :: Delta a -> Delta b -> Delta (a :* b)
  (:+++) :: Delta a -> Delta b -> Delta (a :+ b)
  -- LeftD  :: Delta a -> Delta (a :+ b)
  -- RightD :: Delta b -> Delta (a :+ b)
  -- IsoD :: (a -> r) -> (r -> a) -> Delta r -> Delta a

applyD :: Delta a -> Unop a
applyD (ConstD a)   = const a
applyD IdD          = id
applyD (da :*** db) = applyD da *** applyD db
applyD (da :+++ db) = applyD da +++ applyD db

-- applyD (LeftD  da)  = applyD da +++ error "applyD: LeftD given Right"
-- applyD (RightD db)  = error "applyD: RightD given Left" +++ applyD db
-- applyD (IsoD ar ra dr) = ra . applyD dr . ar

instance Monoid (Delta a) where
  mempty = IdD
  ConstD a `mappend` _ = ConstD a
  IdD `mappend` b = b
  a `mappend` IdD = a
  (f :*** g) `mappend` (splitP -> (h,k)) = (f `mappend` h) :*** (g `mappend` k)
  (f :+++ g) `mappend` (splitS -> (h,k)) = (f `mappend` h) :+++ (g `mappend` k)

splitP :: Delta (a :* b) -> Delta a :* Delta b
splitP (da :*** db)   = (da,db)
splitP (ConstD (a,b)) = (ConstD a, ConstD b)
splitP IdD            = (IdD,IdD)

splitS :: Delta (a :+ b) -> Delta a :* Delta b
splitS (da :+++ db)        = (da,db)
splitS (ConstD (Left da))  = (ConstD da, IdD)
splitS (ConstD (Right db)) = (IdD, ConstD db)
splitS IdD                 = (IdD,IdD)

-- splitS :: Delta (a :+ b) -> Delta a :+ Delta b
-- splitS (LeftD da)          = Left da
-- splitS (RightD db)         = Right db
-- splitS (ConstD (Left  da)) = Left  (ConstD da)
-- splitS (ConstD (Right db)) = Right (ConstD db)
-- -- splitS IdD                 = (IdD,IdD)

infixr 1 +->
newtype a +-> b = DX (Delta a -> Delta b)

instance Newtype (a +-> b) where
  type O (a +-> b) = Delta a -> Delta b
  pack f = DX f
  unpack (DX f) = f

-- instance Category (+->) where
--   id = pack id
--   (.) = inNew2 (.)

instance Category (+->) where
  id = DX id
  DX g . DX f = DX (g . f)

exlD :: Delta (a :* b) -> Delta a
exlD = exl . splitP

exrD :: Delta (a :* b) -> Delta b
exrD = exr . splitP

-- Spec: applyD (joinP (da,db)) (a,b) = (applyD da a, applyD db b)
joinP :: Delta a :* Delta b -> Delta (a :* b)
joinP (IdD, IdD)           = IdD
joinP (ConstD a, ConstD b) = ConstD (a,b)
joinP (da, db)             = da :*** db

joinS :: Delta a :* Delta b -> Delta (a :+ b)
joinS (IdD, IdD) = IdD
joinS (da, db)   = da :+++ db

-- forkD :: (Delta a -> Delta c) -> (Delta a -> Delta d) -> (Delta a -> Delta (c :* d))
-- (f `forkD` g) da = f da :*** g da

-- joinP :: (Delta a -> Delta c) -> (Delta b -> Delta d) -> (Delta (a :* b) -> Delta (c :* d))
-- (f `joinP` g) (splitP -> (da,db)) =
--   f da :*** g db

inlD :: Delta a -> Delta (a :+ b)
inlD da = da :+++ IdD
-- inlD = LeftD

inrD :: Delta b -> Delta (a :+ b)
inrD da = IdD :+++ da
-- inrD = RightD

instance ProductCat (+->) where
  exl = DX (exl . splitP)
  exr = DX (exr . splitP)
  DX f &&& DX g = DX (joinP . (f &&& g))
  -- (&&&) = inNew2 (\ f g -> uncurry joinP . (f &&& g))
  -- (&&&) = inNew2 (liftA2 joinP)
  -- DX f &&& DX g = DX (liftA2 joinP f g)
  -- DX f &&& DX g = DX (\ da -> f da `joinP` g da)

instance CoproductCat (+->) where
  inl = DX inlD
  inr = DX inrD
  DX f ||| DX g = DX (\ (splitS -> (da,db)) -> f da `mappend` g db)

--   DX f ||| DX g = DX ((f ||| g) . splitS)

-- instance ConstCat (+->) b where
--   const b = DX (const (ConstD b))

-- -- Use AD after generalizing.
-- der :: (a -> b) -> (a +-> b)
-- der _ = error "der called"
-- {-# NOINLINE der #-}

#define Atomic(ty) \
instance Newtype (Delta (ty)) where \
  { type O (Delta (ty)) = Maybe (ty) \
  ; unpack (ConstD x) = Just x \
  ; unpack IdD = Nothing \
  ; pack = maybe IdD ConstD }

Atomic(Bool)
Atomic(Int)
Atomic(Float)
Atomic(Double)

instance Newtype (Delta (a :* b)) where
  type O (Delta (a :* b)) = Delta a :* Delta b
  unpack = splitP
  pack   = joinP

instance Newtype (Delta (a :+ b)) where
  type O (Delta (a :+ b)) = Delta a :* Delta b
  unpack = splitS
  pack   = joinS

-- instance Newtype (Delta (a :+ b)) where
--   type O (Delta (a :+ b)) = Delta a :+ Delta b
--   unpack = splitS
--   pack = LeftD ||| RightD

#endif

#if 0

{--------------------------------------------------------------------
    Another experiment: represent Delta via associated type
--------------------------------------------------------------------}

type Changed = Any  -- maybe absorb def into AtomDel

type AtomDel a = Changed :* a

type Atomic a = Del a ~ AtomDel a

class HasDelta a where
  type Del a
  appD :: Del a -> Unop a
  type Del a = AtomDel a
  default appD :: Atomic a => Del a -> Unop a
  appD (Any changed,new) old = if changed then new else old -- or just new?
  constantD :: a -> Del a
  default constantD :: Atomic a => a -> Del a
  constantD = (Any False, )

constantXD :: HasDelta b => b -> (a -+> b)
constantXD b = XD (const (constantD b))

instance HasDelta ()
instance HasDelta Bool
instance HasDelta Int
instance HasDelta Float
instance HasDelta Double

instance (HasDelta a, HasDelta b) => HasDelta (a :* b) where
  type Del (a :* b) = Del a :* Del b
  appD (da,db) = appD da *** appD db
  constantD = constantD *** constantD

instance (HasDelta a, HasDelta b) => HasDelta (a :+ b) where
  type Del (a :+ b) = Del a :+ Del b
  appD (Left  da) (Left  a) = Left  (appD da a)
  appD (Right db) (Right b) = Right (appD db b)
  appD _ _ = error "appD on sum type: Left/Right mismatch"
  constantD = constantD +++ constantD

infixr 1 -+>
newtype a -+> b = XD (Del a -> Del b)

unXD :: (a -+> b) -> (Del a -> Del b)
unXD (XD f) = f

instance Newtype (a -+> b) where
  type O (a -+> b) = Del a -> Del b
  pack f = XD f
  unpack (XD f) = f

instance Category (-+>) where
  id  = pack id
  (.) = inNew2 (.)

instance ProductCat (-+>) where
  exl   = pack exl
  exr   = pack exr
  (&&&) = inNew2 (&&&)

instance CoproductCat (-+>) where
  inl   = pack inl
  inr   = pack inr
  (|||) = inNew2 (|||)

op1 :: (Atomic a, Atomic b) => (a -> b) -> (a -+> b)
op1 f = XD (fmap f)

op2 :: (Atomic a, Atomic b, Atomic c) => (a -> b -> c) -> (a :* b -+> c)
op2 f = XD (uncurry (liftA2 f))

instance (Atomic a, Num a) => NumCat (-+>) a where
  negateC = op1 negate
  addC    = op2 (+)
  subC    = op2 (-)
  mulC    = op2 (*)
  powIC   = op2 (^)

#endif

{--------------------------------------------------------------------
    Yet another try
--------------------------------------------------------------------}

type AtomDel a = Maybe a

type Atomic a = (HasDelta a, Del a ~ AtomDel a)

class HasDelta a where
  type Del a
  type Del a = AtomDel a
  appD :: Del a -> Unop a
  default appD :: Atomic a => Del a -> Unop a
  appD del old = fromMaybe old del
  zeroD :: Del a
  default zeroD :: Atomic a => Del a
  zeroD = Nothing

instance HasDelta () where
  type Del () = ()
  appD () () = ()
  zeroD = ()

-- instance HasDelta ()

instance HasDelta Bool
instance HasDelta Int
instance HasDelta Float
instance HasDelta Double

instance (HasDelta a, HasDelta b) => HasDelta (a :* b) where
  type Del (a :* b) = Del a :* Del b
  appD (da,db) = appD da *** appD db
  zeroD = (zeroD @a, zeroD @b)

-- Possible sum changes: left-to-right, right-to-left, left change, right change, no change.
-- We can consolidate left-to-right and right-to-left.
-- If 

instance (HasDelta a, HasDelta b) => HasDelta (a :+ b) where
  type Del (a :+ b) = Del a :* Del b
  appD (da,db) = appD da +++ appD db
  zeroD = (zeroD @a, zeroD @b)

infixr 1 -+>
newtype a -+> b = XD { unXD :: Del a -> Del b }

zeroXD :: forall a b. HasDelta b => a -+> b
zeroXD = XD (const (zeroD @b))

instance Newtype (a -+> b) where
  type O (a -+> b) = Del a -> Del b
  pack f = XD f
  unpack (XD f) = f

-- type OkXD = HasDelta

instance Category (-+>) where
  -- type Ok (-+>) = OkXD
  id  = pack id
  (.) = inNew2 (.)

-- instance OpCon (:*) (Sat OkXD) where inOp = Entail (Sub Dict)

instance ProductCat (-+>) where
  exl   = pack exl
  exr   = pack exr
  (&&&) = inNew2 (&&&)

-- instance CoproductCat (-+>) where
--   inl :: forall a b. Ok2 (-+>) a b => a -+> a :+ b
--   inl = pack (\ da -> (da,zeroD @b))
-- --   inl   = pack (inl,)
-- --   inr   = pack (,inr)
-- --   (|||) = inNew2 (|||)


-- atomic1 :: (Atomic a, Atomic b) => (a -> b) -> (a -+> b)
-- atomic1 f = XD (fmap f)

atomic1 :: (Atomic a, Atomic b) => (a -> b) -> a -> (a -+> b)
atomic1 f a = XD $ \ case
  Nothing -> Nothing
  d       -> Just (f (appD d a))

atomic2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> a :* b -> (a :* b -+> c)
atomic2 f ab = XD $ \ case
  (Nothing, Nothing) -> Nothing
  d                  -> Just (f (appD d ab))
