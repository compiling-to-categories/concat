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
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experimenting with incremental computation

module ConCat.Incremental where

import Prelude hiding (id,(.))
-- import qualified Prelude as P
import Data.Maybe (fromMaybe,isNothing)
import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import GHC.Exts (Coercible,coerce)

import Data.Void (Void,absurd)
import Control.Newtype
import Data.Constraint ((:-)(..),Dict(..))

import ConCat.Misc ((:*),(:+),Unop,Binop, inNew2,Parity,R,Yes1)
import ConCat.Rep
import qualified ConCat.Category
import ConCat.AltCat hiding (const,curry,uncurry)
import qualified ConCat.AltCat as A
import ConCat.GAD

-- For DelRep:

import ConCat.Complex
import Data.Monoid
import Control.Applicative (WrappedMonad(..))
import GHC.Generics (Par1(..),U1(..),K1(..),M1(..),(:+:)(..),(:*:)(..),(:.:)(..))
import Data.Functor.Identity (Identity(..))
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Monad.Trans.State (StateT(..))

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

infixl 6 .-., .+^, ^+^

type RepDel a = (HasRep a, HasDelta (Rep a), Delta a ~ Delta (Rep a))

class HasDelta a where
  type Delta a
  type Delta a = Delta (Rep a)
  (^+^) :: HasDelta a => Binop (Delta a)
  default (^+^) :: RepDel a => Binop (Delta a)
  (^+^) = (^+^) @(Rep a)
  (.+^) :: a -> Delta a -> a
  default (.+^) :: RepDel a => a -> Delta a -> a
  a .+^ da = abst (repr a .+^ da)
  (.-.) :: a -> a -> Delta a
  default (.-.) :: ({-Eq a,-} RepDel a) => a -> a -> Delta a
  a' .-. a = repr a' .-. repr a
  zeroD :: Delta a              -- needs an explicit type application
  default zeroD :: RepDel a => Delta a
  zeroD = zeroD @(Rep a)  

#define DelAtom(ty) \
  instance HasDelta (ty) where { \
  ; type Delta (ty) = Maybe (ty) \
  ; da ^+^ Nothing = da \
  ; _  ^+^ Just a  = Just a \
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
  () ^+^ () = ()
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
  (da,db) ^+^ (da',db') = ((^+^) @a da da', (^+^) @b db db')
  (a,b) .+^ (da,db) = (a .+^ da, b .+^ db)
  (a',b') .-. (a,b) = (a' .-. a, b' .-. b)
  zeroD = (zeroD @a, zeroD @b)

instance (HasDelta a, HasDelta b) => HasDelta (a :+ b) where
  -- No change, left, right
  type Delta (a :+ b) = Maybe (Delta a :+ Delta b)
  dab ^+^ Nothing = dab
  Nothing ^+^ dab' = dab'
  Just (Left  da) ^+^ Just (Left  da') = Just (Left  ((^+^) @a da da'))
  Just (Right db) ^+^ Just (Right db') = Just (Right ((^+^) @b db db'))
  _ ^+^ _ = error "(^+^): left/right mismatch"
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
  (df ^+^ df') a = (^+^) @b (df a) (df' a)
  (.+^) = liftA2 (.+^)
  (.-.) = liftA2 (.-.)
  zeroD = \ _ -> zeroD @b

  -- (f .+^ df) a = f a .+^ df a
  -- (f' .-. f) a = f' a .-. f a

-- instance (HasDelta a, HasDelta b) => HasDelta (a -> b) where
--   type Delta (a -> b) = a -> Delta a -> Delta b
--   (f .+^ df) a = f a .+^ df a (zeroD @a)
--   (f' .-. f) a da = f' (a .+^ da) .-. f a
--   zeroD _a _da = zeroD @b

{--------------------------------------------------------------------
    Change transformations
--------------------------------------------------------------------}

infixr 1 -+>
newtype a -+> b = DelX { unDelX :: Delta a -> Delta b }

type instance GDOk (-+>) = Yes1

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
instance OpCon (->) (Sat OkDelX) where inOp = Entail (Sub Dict)

instance ProductCat (-+>) where
  exl   = pack exl
  exr   = pack exr
  (&&&) = inNew2 (&&&)

instance CoproductCat (-+>) where
  inl = pack (Just . Left )
  inr = pack (Just . Right)
  (|||) :: forall a b c. Ok3 (-+>) a b c
        => (a -+> c) -> (b -+> c) -> (a :+ b -+> c)
  DelX f ||| DelX g = DelX (maybe (zeroD @c) (f ||| g))

-- I think that there is no ClosedCat (-+>) instance, but there *is* a ClosedCat
-- (GAD (-+>)) instance, since we get an a to use.

-- applyDX :: HasDelta a => a -> ((a -> b) :* a -+> b)
-- applyDX a = DelX (\ (df,da) -> df a da)

-- -- df :: Delta (a -> b)
-- --    ~  a -> Delta b

-- curryDX :: forall a b c. HasDelta b => (a :* b -+> c) -> (a -+> (b -> c))
-- curryDX (DelX f) = DelX (\ (da :: Delta a) (b :: b) (db :: Delta b) -> f (da,db))
--                    -- DelX (\ da b' -> f (da,b' .-. b))

#if 0
  
b                 :: b

f                 :: Delta (a :* b) -> Delta c
                  ~  Delta a :* Delta b -> Delta c

     da           :: a
         b'       ::    b
         b' .-. b :: Delta b
f ( da, b' .-. b) :: Delta c

#endif

atomicD1 :: (Atomic a, Atomic b) => (a -> b) -> a -> (a -+> b)
atomicD1 f a = DelX $ \ case
  Nothing -> Nothing
  d       -> Just (f (a .+^ d))

atomicD2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> a :* b -> (a :* b -+> c)
atomicD2 f ab = DelX $ \ case
  (Nothing, Nothing) -> Nothing
  d                  -> Just (f (ab .+^ d))

instance (r ~ Rep a, Delta a ~ Delta r) => RepCat (-+>) a r where
  reprC = DelX id
  abstC = DelX id

instance Coercible (Delta a) (Delta b) => CoerceCat (-+>) a b where
  coerceC = DelX coerce

-- foo :: (V R R (V R (R, R) R) -> (:*:) (V R R) (V R R) (V R (R, R) R))
--     -+> (L R (R, R) R -> L R (R, R) (R, R))
-- foo = coerceC

-- instance ( Num s, Diagonal (V s a)
--          , Coercible (Rep (L s a a)) (Rep (L s a b))
--          ) => CoerceCat (L s) a b where
--   coerceC = L (coerce (idL :: Rep (L s a a)))

{--------------------------------------------------------------------
    HasRep
--------------------------------------------------------------------}

#define DelRep(ty) instance RepDel (ty) => HasDelta (ty)

-- a :: a
-- da :: Delta (Rep a)
-- repr a :: Rep a
-- repr 

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

DelRep(U1 p)
DelRep(Par1 p)
DelRep(K1 i c p)
DelRep(M1 i c f p)
DelRep((f :+: g) p)
DelRep((f :*: g) p)
DelRep((g :.: f) p)

DelRep(Parity)

DelRep(L s a b)

--     • The constraint ‘HasRep t’ is no smaller than the instance head
--       (Use UndecidableInstances to permit this)

-- foo :: (Int, Int, Int, Int) -+> ((Int :* Int) :* (Int :* Int))
-- foo = reprC :: (Int,Int,Int,Int) -+> ((Int :* Int) :* (Int :* Int))

{--------------------------------------------------------------------
    Use with generalized automatic differentiation
--------------------------------------------------------------------}

type Inc = GD (-+>)

instance TerminalCat Inc where
  -- it = linearD (const ()) zeroDelX
  -- it = D (const ((),constantDelX ()))
  it = A.const ()
  {-# INLINE it #-}

instance HasDelta b => ConstCat Inc b where
  const b = D (const (b, zeroDelX))
  {-# INLINE const #-}

instance ClosedCat Inc where
  apply = applyInc
  curry = curryInc

applyInc :: forall a b. Ok2 Inc a b => Inc ((a -> b) :* a) b
applyInc = D (\ (f,a) -> let (b,DelX f') = andDeriv f a in
              (b, DelX (\ (df,da) -> (^+^) @b (f' da) (df (a .+^ da)))))

#if 0
f :: a -> b
a :: a
b :: b
DelX f' :: a -+> b
f' :: Delta a -> Delta b

df :: a -> Delta b
da :: Delta a

f' da :: Delta b
#endif

curryInc :: forall a b c. HasDelta b => Inc (a :* b) c -> Inc a (b -> c)
curryInc (D (unfork -> (f,f'))) =
  D (\ a -> (curry f a, DelX (\ da b -> unpack (f' (a,b)) (da, zeroD @b))))

-- Note efficiency loss with the unfork.

#if 0

f :: a :* b -> c
f' :: a :* b -> a :* b -+> c

f' (a,b) :: a :* b -+> c
unpack (f' (a,b)) :: Delta a :* Delta b -> Delta c

#endif

--   curry :: forall a b c. Inc (a :* b) c -> Inc a (b -> c)
--   curry (D (f :: a :* b -> c :* (a :* b -+> c))) = D $ \ (a :: a) ->
--     let g  :: b -> c
--         -- g' :: b -> Delta a :* Delta b -> Delta c
--         g' :: b -> (a :* b -+> c)
--         (g,g') = unfork (curry f a)
--         g'' :: b -> Delta a :* Delta b -> Delta c
--         g'' = unpack . g'
--     in
--       (g,DelX (\ (da :: Delta a) (b :: b) -> 
--       -- (g,DelX (\ (da :: Delta a) (b :: b) -> g'' b (da,_)))
--       -- (g, DelX (\ (da :: Delta a) (b' :: b) -> _))


-- unpack . g' :: b -> Delta a :* Delta b -> Delta c

--                           (curry f a, DelX undefined))
                -- D (\ a -> let b = f a in (b, undefined))

-- curryDX :: HasDelta b => b -> (a :* b -+> c) -> (a -+> (b -> c))


#if 0
D f :: Inc (a :* b)  c
f :: a :* b -> c :* (a :* b -+> c)

curry f :: a -> b -> c :* (a :* b -+> c)
curry f a :: b -> c :* (a :* b -+> c)
g :: b -> c
g' :: b -> (a :* b -+> c)
g'' :: b -> Delta a :* Delta b -> Delta c

a :: a
b :: b

a .+^ da :: a


curry (D f) :: Inc a (b -> c)
            =~ a -> (b -> c) :* (a -+> (b -> c))
            =~ a -> (b -> c) :* (Delta a -> Delta (b -> c))
            ~  a -> (b -> c) :* (Delta a -> b -> Delta c)
            =~ a -> (b -> c :* (Delta a -> Delta c))
            =~ a :* b -> c :* (Delta a -> Delta c)

curry (D f) :: Inc a (b -> c)
unpack (curry (D f)) :: a -> (b -> c) :* (a -+> (b -> c))
second unpack . unpack (curry (D f))
            :: a -> (b -> c) :* (Delta a -> Delta (b -> c))
            ~  a -> (b -> c) :* (Delta a -> b -> Delta c)
            =~ a -> (b -> c :* (Delta a -> Delta c))
            =~ a :* b -> c :* (Delta a -> Delta c)

_want :: Delta c

f :: a -> b :* (a -+> b)
                  Delta (a :* b) -> Delta c
  :: Delta a :* Delta b -> Delta c

h :: a -> b :* (Delta a -> Delta (b -> c))
  :: a -> b :* (Delta a -> b -> Delta c)
#endif

-- TODO: Work on unifying more instances between D s and Inc.

atomicI1 :: (Atomic a, Atomic b) => (a -> b) -> Inc a b
atomicI1 f = D (\ a -> (f a, atomicD1 f a))

atomicI2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> Inc (a :* b) c
atomicI2 f = D (\ ab -> (f ab, atomicD2 f ab))

-- atomicI1' :: (Atomic a, Atomic b) => (a -> b) -> Inc a b
-- atomicI1' f = D (\ a -> (f a, DelX (\ case  Nothing -> Nothing
--                                             d       -> Just (f (a .+^ d)))))

-- atomicI2' :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> Inc (a :* b) c
-- atomicI2' f = D (\ ab -> (f ab, DelX (\ case  (Nothing, Nothing) -> Nothing
--                                               d                  -> Just (f (ab .+^ d)))))

instance (Atomic s, Num s) => NumCat Inc s where
  negateC = atomicI1 negateC
  addC    = atomicI2 addC
  subC    = atomicI2 subC
  mulC    = atomicI2 mulC
  powIC   = atomicI2 powIC
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

andInc :: forall a b . (a -> b) -> (a :* Delta a -> b :* Delta b)
andInc _ = error "andInc called"
{-# NOINLINE andInc #-}
{-# RULES "andInc" forall f. andInc f = flatInc (andDeriv f) #-}
-- {-# ANN andInc PseudoFun #-}

flatInc :: (a -> b :* (a -+> b)) -> (a :* Delta a -> b :* Delta b)
flatInc f (a,da) = (b, d da) where (b,DelX d) = f a

dinc :: forall a b . (a -> b) -> (a -> (a -+> b))
dinc _ = error "dinc called"
{-# NOINLINE dinc #-}
{-# RULES "dinc" dinc = deriv #-}

inc :: forall a b . (a -> b) -> (a :* Delta a -> Delta b)
inc _ = error "inc called"
{-# NOINLINE inc #-}
{-# RULES "inc" forall f. inc f = snd . andInc f #-}
-- {-# RULES "inc" forall f. inc f = P.uncurry (unDelX P.. snd P.. andInc f) #-}
-- {-# ANN inc PseudoFun #-}
