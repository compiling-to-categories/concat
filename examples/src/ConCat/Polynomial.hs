{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-orphans #-} -- see orphans

-- | Category of polynomials

module ConCat.Polynomial where

import Prelude hiding (id,(.),zipWith)
import Control.Applicative (liftA2)
import GHC.Generics ((:*:)(..),(:.:)(..),Par1(..),U1(..))

import Data.Pointed (Pointed(..))
import Data.Key (Zip(..))
import Control.Newtype (Newtype(..))
import Data.Constraint (Constraint,Dict(..),(:-)(..))

import ConCat.Misc ((:*),Binop,inNew,inNew2)
import ConCat.Category
import ConCat.Free.VectorSpace
import ConCat.Orphans (fstF,sndF)

-- type OkPolyF b = (Pointed b, Zip b)
type OkPolyF b = (Applicative b, Applicative (PolyF b))

-- Poly R = []
-- Poly (a,b) = Poly a :.: Poly b

class Functor (PolyF a) => HasPoly a where
  type PolyF (a :: * -> *) :: * -> *
  evalP :: Num s => a s -> PolyF a s -> s
  constP :: w -> PolyF a w
  zeroP :: PolyF a w
  idP :: Num s => a (PolyF a s)
  zipWithP :: Binop w -> Binop (PolyF a w)

-- Addition of polynomial representations
addP :: forall a s. (HasPoly a, Num s) => Binop (PolyF a s)
addP = zipWithP @a (+)

-- TODO: generalize from Num to Semiring

-- liftP :: forall a b s. (Functor (PolyF b), HasPoly a) => PolyF b s -> PolyF b (PolyF a s)
-- liftP = fmap (constP @a)

compP :: forall a b s . (HasPoly a, HasPoly b, Num (PolyF a s)) => PolyF b s -> b (PolyF a s) -> PolyF a s
b `compP` ab = evalP ab (fmap (constP @a) b)

compPs :: forall a b c s . (HasPoly a, HasPoly b, Functor c, Num (PolyF a s))
       => c (PolyF b s) -> b (PolyF a s) -> c (PolyF a s)
bc `compPs` ab = flip (compP @a) ab <$> bc

#if 0

                            b :: PolyF b s
      ab                      :: b (PolyF a s)
          fmap (constP @a) b  :: PolyF b (PolyF a s)
evalP ab (fmap (constP @a) b) :: PolyF a s

#endif

instance HasPoly U1 where
  type PolyF U1 = U1
  evalP :: Num s => U1 s -> U1 s -> s
  evalP U1 U1 = 0
  constP _ = U1
  zeroP = U1
  idP = U1
  zipWithP _ U1 U1 = U1

instance HasPoly Par1 where
  type PolyF Par1 = []  -- Could be any foldable
  evalP :: Num s => Par1 s -> [s] -> s
  evalP (Par1 s) = foldr (\ w z -> w + s * z) 0
  constP w = [w]
  zeroP = []
  idP = Par1 [0,1]
  zipWithP :: Binop w -> Binop [w]
  zipWithP op = go
   where
     go [] [] = []
     go as [] = as
     go [] bs = bs
     go (a:as) (b:bs) = (a `op` b) : go as bs

instance (HasPoly a, HasPoly b, Functor a, Functor b) => HasPoly (a :*: b) where
  type PolyF (a :*: b) = PolyF a :.: PolyF b
  evalP :: Num s => (a :*: b) s -> (PolyF a :.: PolyF b) s -> s
  evalP (a :*: b) = evalP a . fmap (evalP b) . unComp1
  constP :: w -> PolyF (a :*: b) w
  constP = Comp1 . constP @a . constP @b
  zeroP :: forall w. PolyF (a :*: b) w
  zeroP = Comp1 (zeroP @a @(PolyF b w))
  idP :: Num s => (a :*: b) (PolyF (a :*: b) s)
  idP = Comp1 <$> ((fmap.fmap) (constP @b) (idP @a) :*: fmap (constP @a) (idP @b))
  zipWithP :: Binop w -> Binop ((PolyF a :.: PolyF b) w)
  zipWithP = inNew2 . zipWithP @a . zipWithP @b

#if 0

ab  :: PolyF a (PolyF b w)
ab' :: PolyF a (PolyF b w)

idP @a :: a (PolyF a s)
idP @b :: b (PolyF b s)

need :: (a :*: b) (PolyF (a :*: b) s)
     :: (a :*: b) ((PolyF a :.: PolyF b) s)

liftP  <$> idP @a :: a (PolyF a (PolyF b s))
constP <$> idP @b :: b (PolyF a (PolyF b s))

           (liftP <$> idP @a) :*: (constP <$> idP @b)  :: (a :*: b) (PolyF a (PolyF b s))
Comp1 <$> ((liftP <$> idP @a) :*: (constP <$> idP @b)) :: (a :*: b) ((PolyF a :.: PolyF b) s)
                                                       :: (a :*: b) (PolyF (a :*: b) s)

#endif

-- Warm-ups

id0 :: Num s => PolyF U1 s
id0 = U1

id1 :: Num s => PolyF Par1 s
id1 = [0,1]

t1 :: Num s => s
t1 = evalP (Par1 3) id1

exl2 :: Num s => PolyF (Par1 :*: Par1) s
exl2 = Comp1 [[],[1]]

t2 :: Num s => s
t2 = evalP (Par1 3 :*: Par1 4) exl2

exr2 :: Num s => PolyF (Par1 :*: Par1) s
exr2 = Comp1 [[0,1]]

t3 :: Num s => s
t3 = evalP (Par1 3 :*: Par1 4) exr2

-- | Polynomials on structures of s values
data Poly s a b = Poly (V s b (PolyF (V s a) s))

instance Newtype (Poly s a b) where
  type O (Poly s a b) = V s b (PolyF (V s a) s)
  pack ps = Poly ps
  unpack (Poly ps) = ps

-- The semantic functor
evalPoly :: (HasV s a, HasPoly (V s a), OkPoly s b)
         => Poly s a b -> (a -> b)
evalPoly (Poly ps) a = unV (evalP (toV a) <$> ps)

-- Define the instances of Category etc so that evalPoly is a homomorphism.

class    (Num s, HasV s a, HasPoly (V s a), OkPolyF (V s a), Num (PolyF (V s a) s)) => OkPoly s a
instance (Num s, HasV s a, HasPoly (V s a), OkPolyF (V s a), Num (PolyF (V s a) s)) => OkPoly s a

instance Category (Poly s) where
  type Ok (Poly s) = OkPoly s
  id = Poly idP
  (.) :: forall a b c. Ok3 (Poly s) a b c => Poly s b c -> Poly s a b -> Poly s a c
  Poly g . Poly f = Poly (compPs @(V s a) @(V s b) @(V s c) g f)

instance OpCon (:*) (Sat (OkPoly s)) where inOp = Entail (Sub Dict)

instance ProductCat (Poly s) where
  exl :: forall a b. Ok2 (Poly s) a b => Poly s (a :* b) a
  exl = Poly (fstF (idP @ (V s a :*: V s b)))
  exr :: forall a b. Ok2 (Poly s) a b => Poly s (a :* b) b
  exr = Poly (sndF (idP @ (V s a :*: V s b)))
  (&&&) :: forall a c d. Ok3 (Poly s) a c d => Poly s a c -> Poly s a d -> Poly s a (c :* d)
  (&&&) = inNew2 (:*:)

#if 0
  
curryP :: Poly s (a :* b) c -> Poly s a (Poly s b c)
curryP (Poly p) = Poly p

p :: V s c (PolyF (V s (a :* b) s))
  :: V s c (PolyF (V s a :*: V s b) s)
  :: V s c ((PolyF (V s a) :.: PolyF (V s b)) s)

unComp1 <$> p :: V s c (PolyF (V s a) (PolyF (V s b) s))

need :: Poly s a (Poly s b c)
     =~ Poly s a (V s c (PolyF (V s b) s))

#endif

{--------------------------------------------------------------------
    Orphans
--------------------------------------------------------------------}

#define NumF(f) \
instance (Applicative (f), Num a) => Num ((f) a) where \
  { fromInteger = pure . fromInteger \
  ; negate = fmap negate \
  ; (+) = liftA2 (+) \
  ; (-) = liftA2 (-) \
  ; (*) = liftA2 (*) \
  ; abs = fmap abs \
  ; signum = fmap signum \
  }

NumF(U1)
NumF(Par1)
NumF(f :*: g)
NumF(g :.: f)

-- Oh! I don't want these instances, since they don't give *polynomial*
-- arithmetic.

