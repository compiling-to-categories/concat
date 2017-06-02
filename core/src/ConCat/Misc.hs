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

{-# OPTIONS_GHC -Wall #-}

-- | Miscellany

module ConCat.Misc where

-- import Control.Arrow ((&&&))
-- import Unsafe.Coerce (unsafeCoerce)
-- import Data.Type.Equality

import Data.Typeable (Typeable,TypeRep,typeRep,Proxy(..))
import Data.Data (Data)
import Unsafe.Coerce (unsafeCoerce)  -- for oops

import Control.Newtype

{--------------------------------------------------------------------
    Type abbreviations
--------------------------------------------------------------------}

infixl 7 :*
infixl 6 :+
infixr 1 :=>

type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

{--------------------------------------------------------------------
    Helpers for GHC.Generics
--------------------------------------------------------------------}

infixr 1 +->
data (a +-> b) p = Fun1 { unFun1 :: a p -> b p }

-- TODO: resolve name conflict with tries. Using ":->:" for functors fits with
-- other type constructors in GHC.Generics.

instance Newtype ((a +-> b) t) where
  type O ((a +-> b) t) = a t -> b t
  pack = Fun1
  unpack = unFun1

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

class    Yes0
instance Yes0

class    Yes1 a
instance Yes1 a

class    Yes2 a b
instance Yes2 a b

inNew :: (Newtype p, Newtype q) =>
         (O p -> O q) -> (p -> q)
inNew = pack <~ unpack

inNew2 :: (Newtype p, Newtype q, Newtype r) =>
          (O p -> O q -> O r) -> (p -> q -> r)
inNew2 = inNew <~ unpack

-- TODO: use inNew and inNew2 in place of ad hoc versions throughout.

exNew :: (Newtype p, Newtype q) =>
         (p -> q) -> (O p -> O q)
exNew = unpack <~ pack

exNew2 :: (Newtype p, Newtype q, Newtype r) =>
          (p -> q -> r) -> (O p -> O q -> O r)
exNew2 = exNew <~ pack

-- | Compose list of unary transformations
compose :: [Unop a] -> Unop a
compose = foldr (.) id

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
data PseudoFun = PseudoFun deriving (Typeable,Data)

-- Alternatively, we could keep PseudoFun abstract:

-- pseudoFun :: PseudoFun
-- pseudoFun = PseudoFun

-- | Pseudo function to fool GHC's divergence checker
oops :: String -> b
oops str = unsafeCoerce ("Oops --- "++str++" called!")
{-# NOINLINE oops #-}
-- {-# RULES "oops" [0] forall str. oops str = error ("Oops --- "++str++" called!") #-}

bottom :: a
bottom = error "bottom evaluated"
{-# NOINLINE bottom #-}

-- Convenient alternative to typeRep
typeR :: forall a. Typeable a => TypeRep
typeR = typeRep (Proxy :: Proxy a)

type R = Double -- Float

sqr :: Num a => a -> a
sqr a = a * a

magSqr :: Num a => a :* a -> a
magSqr (a,b) = sqr a + sqr b
