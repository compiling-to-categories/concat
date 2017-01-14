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

import Prelude hiding (id,(.),const,curry)
-- import qualified Prelude as P
import Data.Maybe (fromMaybe,isNothing)
import Control.Applicative (liftA2)

import Data.Void (Void,absurd)
import Control.Newtype
import Data.Constraint ((:-)(..),Dict(..))

import ConCat.Misc ((:*),(:+),Unop,inNew2,Parity)
import ConCat.Rep
import qualified ConCat.Category
import ConCat.AltCat
import ConCat.GAD

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

infixl 6 .-., .+^

class HasDelta a where
  type Delta a
  type Delta a = AtomDel a
  (.+^) :: HasDelta a => a -> Delta a -> a
  default (.+^) :: Atomic a => a -> Delta a -> a
  (.+^) = fromMaybe
  zeroD :: Delta a              -- needs an explicit type application
  (.-.) :: a -> a -> Delta a
  default (.-.) :: (Eq a, Atomic a) => a -> a -> Delta a
  new .-. old | new == old = Nothing
              | otherwise  = Just new
  default zeroD :: Atomic a => Delta a
  zeroD = Nothing
  isZeroD :: Delta a -> Bool
  default isZeroD :: Atomic a => Delta a -> Bool
  isZeroD = isNothing

-- Semantic function
appD :: HasDelta a => Delta a -> Unop a
appD = flip (.+^)

-- TODO: Try using HasRep instead of Atomic for default, since there are
-- more of them.

-- Unit can't change.
instance HasDelta () where
  type Delta () = Maybe Void
  () .+^ d = maybe () absurd d
  () .-. () = Nothing
  zeroD = Nothing
  isZeroD = const True

-- instance HasDelta ()

instance HasDelta Bool
instance HasDelta Int
instance HasDelta Float
instance HasDelta Double

instance (HasDelta a, HasDelta b) => HasDelta (a :* b) where
  type Delta (a :* b) = Delta a :* Delta b
  (a,b) .+^ (da,db) = (a .+^ da, b .+^ db)
  (a',b') .-. (a,b) = (a' .-. a, b' .-. b)
  zeroD = (zeroD @a, zeroD @b)
  isZeroD (da,db) = isZeroD @a da && isZeroD @b db

instance (HasDelta a, HasDelta b) => HasDelta (a :+ b) where
  -- No change, left, right
  type Delta (a :+ b) = Maybe (Delta a :+ Delta b)
  (.+^) :: (a :+ b) ->Maybe (Delta a :+ Delta b) -> (a :+ b)
  e .+^ Nothing         = e
  Left  a .+^ Just (Left  da) = Left  (appD da a)
  Right a .+^ Just (Right da) = Right (appD da a)
  _ .+^ _                     = error "appD: left/right mismatch"
  Left  a' .-. Left  a = Just (Left  (a' .-. a))
  Right b' .-. Right b = Just (Right (b' .-. b))
  _        .-. _       = Nothing
  zeroD = Nothing
  isZeroD :: Delta (a :+ b) -> Bool
  isZeroD = maybe True (isZeroD @a ||| isZeroD @b)

instance HasDelta b => HasDelta (a -> b) where
  type Delta (a -> b) = a -> Delta b
  (.+^) = liftA2 (.+^)
  (.-.) = liftA2 (.-.)
  zeroD = \ _ -> zeroD @b
  isZeroD = error "isZeroD for (a -> b): undefined"

  -- (f .+^ df) a = f a .+^ df a
  -- (f' .-. f) a = f' a .-. f a

-- I don't think I really need isZeroD.

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

applyDX :: HasDelta a => a -> ((a -> b) :* a -+> b)
applyDX a = DelX (\ (df,da) -> df (a .+^ da))

--     a         :: a
-- df            :: Delta (a -> b)
-- df            ~  a -> Delta b
--           da  :: Delta  a
--     a .+^ da  :: a
-- df (a .+^ da) :: Delta b

curryDX :: HasDelta b => b -> (a :* b -+> c) -> (a -+> (b -> c))
curryDX b (DelX f) = DelX (\ da b' -> f (da,b' .-. b))

-- xf                 :: Delta (a :* b) -> Delta c
--                    ~  Delta a :* Delta b -> Delta c
--      da            :: a
--          b'        ::    b
-- b                  :: b
--          b' .-. b  :: Delta b
-- xf ( da, b' .-. b) :: Delta c

#if 1
atomic1 :: (Atomic a, Atomic b) => (a -> b) -> a -> (a -+> b)
atomic1 f a = DelX $ \ case
  Nothing -> Nothing
  d       -> Just (f (appD d a))

atomic2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> a :* b -> (a :* b -+> c)
atomic2 f ab = DelX $ \ case
  (Nothing, Nothing) -> Nothing
  d                  -> Just (f (appD d ab))
#else
-- These definitions are somewhat more general but generate more complex
-- circuits. It might be that we just lose some optimizations specific to
-- circuits and the Maybe encoding.
atomic1 :: forall a b. (HasDelta a, Atomic b)
        => (a -> b) -> a -> (a -+> b)
atomic1 f a = DelX $ \ d -> if isZeroD @a d then zeroD @b else Just (f (appD d a))

atomic2 :: forall a b c. (HasDelta a, HasDelta b, Atomic c)
        => (a :* b -> c) -> a :* b -> (a :* b -+> c)
atomic2 f ab = DelX $ \ d -> if isZeroD @(a :* b) d then zeroD @c else Just (f (appD d ab))
#endif

instance (r ~ Rep a, Delta a ~ Delta r) => RepCat (-+>) a r where
  reprC = DelX id
  abstC = DelX id

{--------------------------------------------------------------------
    HasRep
--------------------------------------------------------------------}

#define DelRep(ty) \
  instance (HasRep (ty), HasDelta (Rep (ty))) => HasDelta (ty) where { \
  ; type Delta (ty) = Delta (Rep (ty)) \
  ; a .+^ da = abst (repr a .+^ da) \
  ; a' .-. a = repr a' .-. repr a \
  ; zeroD = zeroD @(Rep (ty)) \
  ; isZeroD = isZeroD @(Rep (ty)) \
  }; \

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

-- foo :: (Int, Int, Int, Int) -+> ((Int :* Int) :* (Int :* Int))
-- foo = reprC :: (Int,Int,Int,Int) -+> ((Int :* Int) :* (Int :* Int))

{--------------------------------------------------------------------
    Use with generalized automatic differentiation
--------------------------------------------------------------------}

type Inc = GD (-+>)

instance TerminalCat Inc where
  -- it = linearD (const ()) zeroDelX
  -- it = D (const ((),constantDelX ()))
  it = const ()
  {-# INLINE it #-}

instance HasDelta b => ConstCat Inc b where
  const b = D (const (b, zeroDelX))
  {-# INLINE const #-}

-- instance ClosedCat Inc where
--   apply = D (\ (f,a) -> (f a, applyDX a))
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

fullI1 :: (Atomic a, Atomic b) => (a -> b) -> Inc a b
fullI1 f = D (\ a -> (f a, atomic1 f a))

fullI2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> Inc (a :* b) c
fullI2 f = D (\ ab -> (f ab, atomic2 f ab))

instance (Atomic s, Num s) => NumCat Inc s where
  negateC = fullI1 negateC
  addC    = fullI2 addC
  subC    = fullI2 subC
  mulC    = fullI2 mulC
  powIC   = fullI2 powIC
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

inc :: forall a b . (a -> b) -> (a :* Delta a -> Delta b)
inc _ = error "inc called"
{-# NOINLINE inc #-}
{-# RULES "inc" forall f. inc f = snd . andInc f #-}
-- {-# RULES "inc" forall f. inc f = P.uncurry (unDelX P.. snd P.. andInc f) #-}
-- {-# ANN inc PseudoFun #-}
