{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -Wno-deprecations #-} -- for errorWithStackTrace

-- | Miscellany

module ConCat.Misc where

import GHC.Types (Constraint)

-- import Control.Arrow ((&&&))
-- import Data.Type.Equality

import Data.Typeable (Typeable,TypeRep,typeRep,Proxy(..))
import Data.Data (Data)
import Data.Monoid (Endo(..))
import Data.Complex (Complex)
import GHC.Generics hiding (R)
-- import Unsafe.Coerce (unsafeCoerce)  -- for oops
import GHC.Stack (errorWithStackTrace)  -- for oops
import GHC.TypeLits

import Control.Newtype

{--------------------------------------------------------------------
    Type abbreviations
--------------------------------------------------------------------}

infixr 8 :^
infixl 7 :*
infixl 6 :+
infixr 1 :=>

type s :^ n = n -> s
type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

{--------------------------------------------------------------------
    Helpers for GHC.Generics
--------------------------------------------------------------------}

-- | Operate inside a Generic1
inGeneric1 :: (Generic1 f, Generic1 g) => (Rep1 f a -> Rep1 g b) -> (f a -> g b)
inGeneric1 = to1 <~ from1
{-# INLINE inGeneric1 #-}

-- | Apply a unary function within the 'Comp1' constructor.
inComp :: (g (f a) -> g' (f' a')) -> ((g :.: f) a -> (g' :.: f') a')
inComp = Comp1 <~ unComp1
{-# INLINE inComp #-}

-- | Apply a binary function within the 'Comp1' constructor.
inComp2 :: (  g (f a)   -> g' (f' a')     -> g'' (f'' a''))
        -> ((g :.: f) a -> (g' :.: f') a' -> (g'' :.: f'') a'')
inComp2 = inComp <~ unComp1
{-# INLINE inComp2 #-}

-- TODO: phase out inComp and inComp2 in favor of inNew and inNew2.

absurdF :: V1 a -> b
absurdF = \ case
{-# INLINE absurdF #-}

-- infixr 1 +->
-- data (a +-> b) p = Fun1 { unFun1 :: a p -> b p }

-- -- TODO: resolve name conflict with tries. Using ":->:" for functors fits with
-- -- other type constructors in GHC.Generics.

-- instance Newtype ((a +-> b) t) where
--   type O ((a +-> b) t) = a t -> b t
--   pack = Fun1
--   unpack = unFun1

#if 0

{--------------------------------------------------------------------
    Evaluation
--------------------------------------------------------------------}

-- class Evalable e where
--   type ValT e
--   eval :: e -> ValT e

class PrimBasics p where
  unitP :: p ()
  pairP :: p (a :=> b :=> a :* b)

class Evalable p where eval :: p a -> a

-- TODO: Are we still using PrimBasics or Evalable?

#endif

{--------------------------------------------------------------------
    Other
--------------------------------------------------------------------}

type Unop   a = a -> a
type Binop  a = a -> Unop a
type Ternop a = a -> Binop a

infixl 1 <~
infixr 1 ~>

-- | Add pre- and post-processing
(~>) :: forall a b a' b'. (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f ~> h) g = h . g . f
-- (~>) = flip (<~)
{-# INLINE (~>) #-}

-- | Add post- and pre-processing
(<~) :: forall a b a' b'. (b -> b') -> (a' -> a) -> ((a -> b) -> (a' -> b'))
(h <~ f) g = h . g . f
{-# INLINE (<~) #-}

-- For SEC-style programming. I was using fmap instead, but my rules interfered.
result :: (b -> c) -> ((a -> b) -> (a -> c))
result = (.)
{-# INLINE result #-}

class    Yes0
instance Yes0

class    Yes1 a
instance Yes1 a

class    Yes2 a b
instance Yes2 a b

-- | Compose list of unary transformations
compose :: Foldable f => f (Unop a) -> Unop a
compose = appEndo . foldMap Endo
-- compose = foldr (.) id

infixr 3 `xor`

xor :: Binop Bool
xor = (/=)
{-# NOINLINE xor #-}

newtype Parity = Parity { getParity :: Bool }

instance Newtype Parity where
  type O Parity = Bool
  pack = Parity
  unpack (Parity x) = x

instance Monoid Parity where
  mempty = Parity False
  Parity a `mappend` Parity b = Parity (a `xor` b)

boolToInt :: Bool -> Int
boolToInt c = if c then 1 else 0
{-# INLINE boolToInt #-}

cond :: a -> a -> Bool -> a
cond t e i = if i then t else e
{-# INLINE cond #-}  -- later INLINE?

{--------------------------------------------------------------------
    Type level computations
--------------------------------------------------------------------}

infixr 3 &&

class    (a,b) => a && b
instance (a,b) => a && b

-- Saying (b,a) instead of (a,b) causes Oks k [a,b,c] to expand in order, oddly.
-- TODO: investigate.

infixr 3 &+&
class    (a t, b t) => (a &+& b) t
instance (a t, b t) => (a &+& b) t

class    f b a => Flip f a b
instance f b a => Flip f a b

-- • Potential superclass cycle for ‘&&’
--     one of whose superclass constraints is headed by a type variable: ‘a’
--   Use UndecidableSuperClasses to accept this

-- Same for Flip

type family FoldrC op b0 as where
  FoldrC op z '[]      = z
  FoldrC op z (a : as) = a `op` FoldrC op z as

type family MapC f us where
  MapC f '[]      = '[]
  MapC f (u : us) = f u : MapC f us

-- type Comp g f u = g (f u)
-- -- Operator applied to too few arguments: :
-- type MapC' f us = FoldrC (Comp (':) f) '[] us

type AndC   cs = FoldrC (&&) Yes0 cs
type AllC f us = AndC (MapC f us)

-- type family AndC' cs where
--   AndC' '[]      = Yes0
--   AndC' (c : cs) = c && AndC' cs

-- type family AllC f as where
--   AllC f '[]      = Yes0
--   AllC f (a : as) = f a && AllC f as

-- -- Operator applied to too few arguments: :
-- type as ++ bs = FoldrC (':) bs as

infixr 5 ++
type family as ++ bs where
  '[]      ++ bs = bs
  (a : as) ++ bs = a : as ++ bs

type family CrossWith f as bs where
  CrossWith f '[]      bs = '[]
  CrossWith f (a : as) bs = MapC (f a) bs ++ CrossWith f as bs

-- Illegal nested type family application ‘MapC (f a1) bs
--                                               ++ CrossWith f as bs’
--       (Use UndecidableInstances to permit this)

type AllC2 f as bs = AndC (CrossWith f as bs)

-- | Annotation for pseudo-function, i.e., defined by rules. During ccc
-- generation, don't split applications. TODO: maybe add an arity.
data PseudoFun = PseudoFun { pseudoArgs :: Int } deriving (Typeable,Data)

-- Alternatively, we could keep PseudoFun abstract:

-- pseudoFun :: Int -> PseudoFun
-- pseudoFun = PseudoFun

-- | Pseudo function to fool GHC's divergence checker.
oops :: String -> b
oops str = errorWithStackTrace ("Oops: "++str)
{-# NOINLINE oops #-}

--     In the use of ‘errorWithStackTrace’ (imported from GHC.Stack):
--     Deprecated: "'error' appends the call stack now"

-- When we use error, the divergence checker eliminates a lot of code early. An
-- alternative is unsafeCoerce, but it leads to terrible run-time errors. A safe
-- alternative seems to be errorWithStackTrace. Oddly, the doc for
-- errorWithStackTrace says "Deprecated: error appends the call stack now."

-- | Hack: delay inlining to thwart some of GHC's rewrites
delay :: a -> a
delay a = a
{-# INLINE [0] delay #-}

bottom :: a
-- bottom = error "bottom evaluated"
bottom = oops "bottom evaluated"
{-# NOINLINE bottom #-}

-- Convenient alternative to typeRep
typeR :: forall a. Typeable a => TypeRep
typeR = typeRep (Proxy :: Proxy a)

type R = Double -- Float

type C = Complex R

sqr :: Num a => a -> a
sqr a = a * a
{-# INLINE sqr #-}

magSqr :: Num a => a :* a -> a
magSqr (a,b) = sqr a + sqr b
{-# INLINE magSqr #-}

transpose :: (Traversable t, Applicative f) => t (f a) -> f (t a)
transpose = sequenceA

inTranspose :: (Applicative f, Traversable t, Applicative f', Traversable t')
            => (f (t a) -> t' (f' a)) -> (t (f a) -> f' (t' a))
inTranspose = transpose <~ transpose
{-# INLINE inTranspose #-}
-- inTranspose h = transpose . h . transpose

unzip :: Functor f => f (a :* b) -> f a :* f b
unzip ps = (fst <$> ps, snd <$> ps)
{-# INLINE unzip #-}

natValAt :: forall n. KnownNat n => Integer
natValAt = nat @n

-- Shorter name
nat :: forall n. KnownNat n => Integer
nat = natVal (Proxy @n)

int :: forall n. KnownNat n => Int
int = fromIntegral (natValAt @n)

{--------------------------------------------------------------------
    Newtype
--------------------------------------------------------------------}

-- See <https://github.com/jcristovao/newtype-generics/pull/5>

-- Type generalization of underF from newtype-generics.
underF :: (Newtype n, Newtype n', o' ~ O n', o ~ O n, Functor f, Functor g)
       => (o -> n) -> (f n -> g n') -> (f o -> g o')
underF _ f = fmap unpack . f . fmap pack
{-# INLINE underF #-}

-- Type generalization of overF from newtype-generics.
overF :: (Newtype n, Newtype n', o' ~ O n', o ~ O n, Functor f, Functor g)
      => (o -> n) -> (f o -> g o') -> (f n -> g n')
overF _ f = fmap pack . f . fmap unpack
{-# INLINE overF #-}

inNew :: (Newtype p, Newtype q) =>
         (O p -> O q) -> (p -> q)
inNew = pack <~ unpack
{-# INLINE inNew #-}

inNew2 :: (Newtype p, Newtype q, Newtype r) =>
          (O p -> O q -> O r) -> (p -> q -> r)
inNew2 = inNew <~ unpack
{-# INLINE inNew2 #-}

-- TODO: use inNew and inNew2 in place of ad hoc versions throughout.

exNew :: (Newtype p, Newtype q) =>
         (p -> q) -> (O p -> O q)
exNew = unpack <~ pack
{-# INLINE exNew #-}

exNew2 :: (Newtype p, Newtype q, Newtype r) =>
          (p -> q -> r) -> (O p -> O q -> O r)
exNew2 = exNew <~ pack
{-# INLINE exNew2 #-}

{--------------------------------------------------------------------
    Constraint shorthands
--------------------------------------------------------------------}

#if 1
-- Experiment. Smaller Core?
type C1 (con :: u -> Constraint) a = con a
type C2 (con :: u -> Constraint) a b = (con a, con b)
type C3 (con :: u -> Constraint) a b c = (con a, con b, con c)
type C4 (con :: u -> Constraint) a b c d = (con a, con b, con c, con d)
type C5 (con :: u -> Constraint) a b c d e = (con a, con b, con c, con d, con e)
type C6 (con :: u -> Constraint) a b c d e f = (con a, con b, con c, con d, con e, con f)
#else
type C1 (con :: u -> Constraint) a = con a
type C2 con a b         = (C1 con a, con b)
type C3 con a b c       = (C2 con a b, con c)
type C4 con a b c d     = (C2 con a b, C2 con c d)
type C5 con a b c d e   = (C3 con a b c, C2 con d e)
type C6 con a b c d e f = (C3 con a b c, C3 con d e f)
#endif
