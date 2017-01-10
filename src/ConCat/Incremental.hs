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

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experimenting with incremental computation

module ConCat.Incremental where

import Prelude hiding (id,(.))
import qualified Prelude as P
import Control.Applicative (liftA2)
import Control.Arrow (Kleisli)

import Data.Void
import Data.Constraint ((:-)(..),Dict(..))
import Control.Newtype

import ConCat.Misc ((:*),(:+),Unop,inNew,inNew2,Yes1)
import qualified ConCat.Category
import ConCat.AltCat hiding (const,curry,uncurry)

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

-- Use AD after generalizing.
der :: (a -> b) -> (a +-> b)
der _ = error "der called"
{-# NOINLINE der #-}

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
    Another experiment: represent Delta via associated type
--------------------------------------------------------------------}

class HasDelta a where
  type Del a
  appD :: Del a -> Unop a
  type Del a = a
  default appD :: Del a ~ a => Del a -> Unop a
  appD = const

instance HasDelta () where
  type Del () = Void
  appD = absurd

instance HasDelta Bool
instance HasDelta Int
instance HasDelta Float
instance HasDelta Double

instance (HasDelta a, HasDelta b) => HasDelta (a :* b) where
  type Del (a :* b) = Del a :* Del b
  appD (da,db) = appD da *** appD db

-- instance (HasDelta a, HasDelta b) => HasDelta (a :+ b) where
--   type Del (a :+ b) = Del a :* Del b
--   appD (da,db) = appD da +++ appD db

instance (HasDelta a, HasDelta b) => HasDelta (a :+ b) where
  type Del (a :+ b) = Del a :+ Del b
  appD (Left  da) (Left  a) = Left  (appD da a)
  appD (Right db) (Right b) = Right (appD db b)
  appD _ _ = error "appD on sum type: Left/Right mismatch"

type XD' a b = Kleisli Maybe (Del a) (Del b)

infixr 1 -+>
newtype a -+> b = XD (XD' a b)

instance Newtype (a -+> b) where
  type O (a -+> b) = XD' a b
  pack f = XD f
  unpack (XD f) = f

instance Category (-+>) where
  -- type Ok (-+>) = Y
  id = pack id
  (.) = inNew2 (.)

#if 0
class    Y a
instance Y a

instance OpCon op (Sat Y) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}
#endif

{-

If I use the default Ok (-+>) = Yes1, I get some errors I don't understand:

    • Overlapping instances for Yes1 (Del a) arising from a use of ‘id’
      Matching instances:
        instance forall k (a :: k). Yes1 a
          -- Defined at /Users/conal/Haskell/concat/src/ConCat/Misc.hs:98:10
      There exists a (perhaps superclass) match:
        from the context: Ok (-+>) a
          bound by the type signature for:
                     id :: Ok (-+>) a => a -+> a
          at /Users/conal/Haskell/concat/src/ConCat/Incremental.hs:210:3-4
      (The choice depends on the instantiation of ‘a’
       To pick the first instance above, use IncoherentInstances
       when compiling the other instance declarations)
    • In the first argument of ‘XD’, namely ‘id’
      In the expression: XD id
      In an equation for ‘id’: id = XD id

    • Could not deduce (Yes1 (Del a), Yes1 (Del b), Yes1 (Del c))
        arising from a use of ‘.’
      from the context: Ok3 (-+>) a b c
        bound by the type signature for:
                   (.) :: Ok3 (-+>) a b c => b -+> c -> a -+> b -> a -+> c
        at /Users/conal/Haskell/concat/src/ConCat/Incremental.hs:211:8
    • In the first argument of ‘XD’, namely ‘(g . f)’
      In the expression: XD (g . f)
      In an equation for ‘.’: (XD g) . (XD f) = XD (g . f)

I'm using IncoherentInstances, but I don't know what will happen.
If it blows up, switch to Y above, and inquire.

-}

instance ProductCat (-+>) where
  exl   = pack exl
  exr   = pack exr
  (&&&) = inNew2 (&&&)

instance CoproductCat (-+>) where
  inl   = pack inl
  inr   = pack inr
  (|||) = inNew2 (|||)

-- volatile :: a -+> a
-- volatile = D (const (

