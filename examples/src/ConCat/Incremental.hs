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
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

#include "ConCat/AbsTy.inc"
AbsTyPragmas

-- | Incremental evaluation via generalized automatic differentiation

module ConCat.Incremental where

import Prelude hiding (id,(.),const,curry,uncurry)
-- import qualified Prelude as P
import Data.Maybe (fromMaybe,isNothing)
import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import GHC.Exts (Coercible,coerce)

import Data.Void (Void,absurd)
import Control.Newtype
import Data.Constraint ((:-)(..),Dict(..))

import ConCat.Misc ((:*),(:+),Unop,Binop, inNew2,Parity,R,Yes1,result)
import ConCat.Rep
import ConCat.Category
import qualified ConCat.AltCat as A
import ConCat.GAD
import ConCat.AdditiveFun

-- For DelRep:

import ConCat.Complex
import Data.Monoid
import Control.Applicative (WrappedMonad(..))
import GHC.Generics (Par1(..),U1(..),K1(..),M1(..),(:+:)(..),(:*:)(..),(:.:)(..))
import Data.Functor.Identity (Identity(..))
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Monad.Trans.State (StateT(..))

AbsTyImports

import ConCat.Free.LinearRow (L)
-- Tests:
import ConCat.Free.VectorSpace (V)
import GHC.Generics ((:*:))

{--------------------------------------------------------------------
    Changes
--------------------------------------------------------------------}

-- Delta for "Atomic" (all-or-nothing) values.
-- Nothing for no change, and Just a for new value a.
type AtomDel a = Maybe a

type Atomic a = (HasDelta a, Delta a ~ AtomDel a)

infixl 6 .-., .+^, @+

type RepDel a = (HasRep a, HasDelta (Rep a), Delta a ~ Delta (Rep a))

class HasDelta a where
  type Delta a
  (@+) :: HasDelta a => Binop (Delta a)
  (.+^) :: a -> Delta a -> a
  (.-.) :: a -> a -> Delta a

  type Delta a = Delta (Rep a)
  default (@+) :: RepDel a => Binop (Delta a)
  (@+) = (@+) @(Rep a)
  default (.+^) :: RepDel a => a -> Delta a -> a
  a .+^ da = abst (repr a .+^ da)
  default (.-.) :: ({-Eq a,-} RepDel a) => a -> a -> Delta a
  a' .-. a = repr a' .-. repr a
  default zeroD :: RepDel a => Delta a
  zeroD :: Delta a              -- needs an explicit type application
  zeroD = zeroD @(Rep a)  

#define DelAtom(ty) \
  instance HasDelta (ty) where { \
  ; type Delta (ty) = Maybe (ty) \
  ; da @+ Nothing = da \
  ; _  @+ Just a  = Just a \
  ; (.+^) = fromMaybe \
  ; new .-. old = if new == old then Nothing else Just new \
  ; zeroD = Nothing \
  }


-- TODO: Use HasRep instead of Atomic for default, since there are
-- more of them.

-- Semantic function
appD :: HasDelta a => Delta a -> Unop a
appD = flip (.+^)

-- Unit can't change.
instance HasDelta () where
  type Delta () = () -- no change
  () @+ () = ()
  () .+^ () = ()
  () .-. () = ()
  zeroD = ()

-- instance HasDelta ()
-- instance HasDelta Bool
-- instance HasDelta Int
-- instance HasDelta Float
-- instance HasDelta Double

DelAtom(Bool)
DelAtom(Int)
DelAtom(Float)
DelAtom(Double)

instance (HasDelta a, HasDelta b) => HasDelta (a :* b) where
  type Delta (a :* b) = Delta a :* Delta b
  (da,db) @+ (da',db') = ((@+) @a da da', (@+) @b db db')
  (a,b) .+^ (da,db) = (a .+^ da, b .+^ db)
  (a',b') .-. (a,b) = (a' .-. a, b' .-. b)
  zeroD = (zeroD @a, zeroD @b)

instance (HasDelta a, HasDelta b) => HasDelta (a :+ b) where
  -- No change, left, right
  type Delta (a :+ b) = Maybe (Delta a :+ Delta b)
  dab @+ Nothing = dab
  Nothing @+ dab' = dab'
  Just (Left  da) @+ Just (Left  da') = Just (Left  ((@+) @a da da'))
  Just (Right db) @+ Just (Right db') = Just (Right ((@+) @b db db'))
  _ @+ _ = error "(@+): left/right mismatch"
  (.+^) :: (a :+ b) -> Maybe (Delta a :+ Delta b) -> (a :+ b)
  e .+^ Nothing         = e
  Left  a .+^ Just (Left  da) = Left  (appD da a)
  Right a .+^ Just (Right da) = Right (appD da a)
  _ .+^ _                     = error "(.+^): left/right mismatch"
  Left  a' .-. Left  a = Just (Left  (a' .-. a))
  Right b' .-. Right b = Just (Right (b' .-. b))
  _        .-. _       = Nothing
  zeroD = Nothing

instance HasDelta b => HasDelta (a -> b) where
  type Delta (a -> b) = a -> Delta b
  (df @+ df') a = (@+) @b (df a) (df' a)
  (.+^) = liftA2 (.+^)
  (.-.) = liftA2 (.-.)
  zeroD = \ _ -> zeroD @b

  -- (f .+^ df) a = f a .+^ df a
  -- (f' .-. f) a = f' a .-. f a

-- instance HasDelta a => Additive (Delta a) where
--   (^+^) = (@+) @a
--   zero = zeroD @a
--
-- Nope:
-- 
--    Illegal type synonym family application in instance: Delta a
--    In the instance declaration for ‘Additive (Delta a)’

instance OpCon (:*) (Sat HasDelta) where inOp = Entail (Sub Dict)
instance OpCon (:+) (Sat HasDelta) where inOp = Entail (Sub Dict)
instance OpCon (->) (Sat HasDelta) where inOp = Entail (Sub Dict)

-- Instead, wrap Delta a:

newtype Del a = Del (Delta a)

instance HasRep (Del a) where
  type Rep (Del a) = Delta a
  abst d = Del d
  repr (Del d) = d

AbsTy(Del a)

instance HasDelta a => Additive (Del a) where
  (^+^) = inAbst2 ((@+) @a)
  zero = abst (zeroD @a)

{--------------------------------------------------------------------
    Change transformations
--------------------------------------------------------------------}

infixr 1 -#>
newtype a -#> b = DelX { unDelX :: Del a -+> Del b }

type Inc = GD (-#>)

instance HasRep (a -#> b) where
  type Rep (a -#> b) = Del a -+> Del b
  abst f = DelX f
  repr (DelX f) = f

AbsTy(a -#> b)

pairD :: Del u :* Del v -+> Del (u :* v)
pairD = abst (uncurry (inAbst2 (,)))
{-# INLINE pairD #-}

unPairD :: Del (u :* v) -+> Del u :* Del v
unPairD = abst (\ (Del (du,dv)) -> (Del du, Del dv))
{-# INLINE unPairD #-}

instance Category (-#>) where
  type Ok (-#>) = HasDelta
  id  = abst id
  (.) = inAbst2 (.)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance ProductCat (-#>) where
  exl   = abst (exl . unPairD)
  exr   = abst (exr . unPairD)
  (&&&) = inAbst2 (\ f g -> pairD . (f &&& g))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

#if 0
-- Types for exl:
      exl            :: Del a :* Del b -+> Del a
      exl . unPairD  :: Del (a :* b) -+> Del a
abst (exl . unPairD) :: a :* b -#> a

-- Types for (&&&):
               f         :: Del a -+> Del c
                     g   :: Del a -+> Del d
               f &&& g   :: Del a -+> Del c :* Del d
      pairD . (f &&& g)  :: Del a -+> Del (c :* d)
abst (pairD . (f &&& g)) :: a -#> c :* d
#endif

instance CoproductPCat (-#>) where
  inlP = abst (pairD . inlP)
  inrP = abst (pairD . inrP)
  (||||) = inAbst2 (\ f g -> (f |||| g) . unPairD)
  {-# INLINE inlP #-}
  {-# INLINE inrP #-}
  {-# INLINE (||||) #-}

#if 0
-- Types for inlP:
              inlP  :: Del a -+> Del a :* Del b
      pairD . inlP  :: Del a -+> Del (a :* b)
abst (pairD . inlP) :: a -#> a :* b

-- Types for (||||):
               f            :: Del a -+> Del c
                     g      :: Del b -+> Del c
               f |||| g     :: Del a :* Del b -+> Del c
      (f |||| g) . unPairD  :: Del (a :* b) -+> Del c
abst ((f |||| g) . unPairD) :: a :* b -#> c
#endif

atomicD1 :: (Atomic a, Atomic b) => (a -> b) -> (a -#> b)
atomicD1 = abst . abst . inAbst . fmap
-- atomicD1 f = abst $ abst $ inAbst $ fmap f

#if 0
                         f    :: a -> b
                    fmap f    :: Maybe a -> Maybe b
            inAbst (fmap f)   :: Del a -> Del b
      abst (inAbst (fmap f))  :: Del a -+> Del b
abst (abst (inAbst (fmap f))) :: a -#> b
#endif

-- Similar to liftA2 on Maybe, but yields a Just when either argument does.
orMaybe :: (a :* b -> c) -> a :* b -> (Maybe a :* Maybe b -> Maybe c)
orMaybe _ (_,_) (Nothing,Nothing) = Nothing
orMaybe f (_,b) (Just a',Nothing) = Just (f (a',b ))
orMaybe f (a,_) (Nothing,Just b') = Just (f (a ,b'))
orMaybe f (_,_) (Just a',Just b') = Just (f (a',b'))

atomicD2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> (a :* b) -> (a :* b -#> c)
atomicD2 f dab = abst $ abst $ inAbst $ orMaybe f dab

#if 0

                    orMaybe f dab    :: Maybe a :* Maybe b -> Maybe c
                                     :: Delta (a :* b) -> Delta c
            inAbst (orMaybe f dab)   :: Del (a :* b) -> Del c
      abst (inAbst (orMaybe f dab))  :: Del (a :* b) -+> Del c
abst (abst (inAbst (orMaybe f dab))) :: (a :* b) -#> c
#endif

-- instance Atomic a => ScalarCat (-#>) a where
--   scale s = atomicD1 (* s)

atomic1 :: (Atomic a, Atomic b) => (a -> b) -> GD (-#>) a b
atomic1 f = D (f &&& const (atomicD1 f))

atomic2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> GD (-#>) (a :* b) c
atomic2 f = D (f &&& atomicD2 f)

instance {-# overlapping #-} (Num s, Additive s, Atomic s) => NumCat Inc s where
  negateC = atomic1 negateC
  addC    = atomic2 addC
  subC    = atomic2 subC
  mulC    = atomic2 mulC
  powIC   = error "powIC: not yet defined on IF"
  {-# INLINE negateC #-}
  {-# INLINE addC #-}
  {-# INLINE subC #-}
  {-# INLINE mulC #-}
  {-# INLINE powIC #-}


{--------------------------------------------------------------------
    "Differentiation" interface
--------------------------------------------------------------------}

andInc :: forall a b . (a -> b) -> (a -> b :* (Delta a -> Delta b))
andInc f = (result.second) (inRepr.repr.repr) (repr (A.toCcc @Inc f))
{-# INLINE andInc #-}

--                                     toCcc @Inc f         :: GD (-#>) a b
--                              repr  (toCcc @Inc f)        :: a -> b :* (a -#> b)
-- (result.second)              repr  (repr (toCcc @Inc f)) :: a -> b :* (Del a -+> Del b)
-- (result.second) (       repr.repr) (repr (toCcc @Inc f)) :: a -> b :* (Del a -> Del b)
-- (result.second) (inRepr.repr.repr) (repr (toCcc @Inc f)) :: a -> b :* (Delta a -> Delta b)

inc :: forall a b . (a -> b) -> (a -> Delta a -> Delta b)
inc f = result snd (andInc f)
{-# INLINE inc #-}
