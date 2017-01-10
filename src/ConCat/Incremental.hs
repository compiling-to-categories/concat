{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experimenting with incremental computation

module ConCat.Incremental where

import Prelude hiding (id,(.))
import Control.Applicative (liftA2)

import Control.Newtype

import ConCat.Misc ((:*),(:+),Unop,inNew,inNew2)
import qualified ConCat.Category
import ConCat.AltCat hiding (const,curry,uncurry)

data Delta :: * -> * where
  ConstD :: a        -> Delta a
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
joinS (IdD, IdD)           = IdD
joinS (da, db)             = da :+++ db

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

-- Use AD after generalizing.
der :: (a -> b) -> (a +-> b)
der _ = error "der called"
{-# NOINLINE der #-}

instance Newtype (Delta ()) where
  type O (Delta ()) = ()
  unpack = const ()
  pack = const IdD

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

{--------------------------------------------------------------------
    Simpler: use Unop in place of Delta
--------------------------------------------------------------------}

newtype a *-> b = DU (Unop a -> Unop b)

instance Category (*->) where
  id = DU id
  DU g . DU f = DU (g . f)

-- I can define (&&&), but not exl or exr.

-- instance ProductCat (*->) where
--   DU f &&& DU g = DU (\ da -> f da *** g da)

