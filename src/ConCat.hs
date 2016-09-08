{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-} -- experiment
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- #define DefaultCat

-- | Constrained categories

module ConCat where

import Prelude hiding (id,(.),curry,uncurry)
import qualified Prelude as P
#ifdef DefaultCat
import qualified Control.Category as C
#endif
import Control.Arrow (Kleisli(..),arr)
import qualified Control.Arrow as A
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import Data.Proxy (Proxy)
import GHC.Generics
import GHC.Types (Constraint)
import Data.Constraint hiding ((&&&),(***),(:=>))
import qualified Data.Constraint as C

import Control.Newtype (Newtype(..))

import Data.MemoTrie

import Misc hiding ((<~),(~>))
import Orphans ()

{--------------------------------------------------------------------
    Constraint utilities
--------------------------------------------------------------------}

-- Lower fixity
infixr 1 |-
type (|-) = (:-)

infixl 1 <+
-- | Synonym for '(\\)'
(<+) :: a => (b => r) -> (a |- b) -> r
(<+) = (\\)

class    (a,b) => a && b
instance (a,b) => a && b

-- • Potential superclass cycle for ‘&&’
--     one of whose superclass constraints is headed by a type variable: ‘a’
--   Use UndecidableSuperClasses to accept this

conj :: (a,b) |- a && b
conj = Sub Dict

unconj :: a && b |- (a,b)
unconj = Sub Dict

{--------------------------------------------------------------------
    Constraints with product consequences
--------------------------------------------------------------------}

type UnitCon con = con ()

class OpCon op con where
  inOp :: con a && con b |- con (a `op` b)

inOpL :: OpCon op con => (con a && con b) && con c |- con ((a `op` b) `op` c)
inOpL = inOp . first  inOp

inOpR :: OpCon op con => con a && (con b && con c) |- con (a `op` (b `op` c))
inOpR = inOp . second inOp

inOpL' :: OpCon op con 
       => (con a && con b) && con c |- con (a `op` b) && con ((a `op` b) `op` c)
inOpL' = second inOp . rassocP . first (dup . inOp)

-- (con a && con b) && con c
-- con (a `op` b) && con c
-- (con (a `op` b) && con (a `op` b)) && con c
-- con (a `op` b) && (con (a `op` b) && con c)
-- con (a `op` b) && con ((a `op` b) `op` c)

inOpR' :: OpCon op con => con a && (con b && con c) |- con (a `op` (b `op` c)) &&  con (b `op` c)
inOpR' = first inOp . lassocP . second (dup . inOp)

inOpLR :: forall op con a b c. OpCon op con =>
  ((con a && con b) && con c) && (con a && (con b && con c))
  |- con ((a `op` b) `op` c) && con (a `op` (b `op` c))
inOpLR = inOpL *** inOpR


instance OpCon op Yes where
  inOp = Sub Dict

-- type C1 (con :: u -> Constraint) a = con a
-- type C2 con a b         = (C1 con a, con b)

type C2 (con :: u -> Constraint) a b = (con a, con b)

type C3 con a b c       = (C2 con a b, con c)
type C4 con a b c d     = (C3 con a b c, con d)
type C5 con a b c d e   = (C4 con a b c d, con e)
type C6 con a b c d e f = (C5 con a b c d e, con f)

type Ok2 k a b         = C2 (Ok k) a b
type Ok3 k a b c       = C3 (Ok k) a b c
type Ok4 k a b c d     = C4 (Ok k) a b c d
type Ok5 k a b c d e   = C5 (Ok k) a b c d e
type Ok6 k a b c d e f = C6 (Ok k) a b c d e f

-- -- TODO. Try out this more convenient alternative to inOp
-- inOp' :: forall op k a b. OpCon (op k) (Ok k)
--       => Ok k a && Ok k b |- Ok k (op k a b)
-- inOp' = inOp

class OpCon' k op con where
  inOp' :: (Ok k (con a), Ok k (con b)) => Prod k (con a) (con b) `k` con (a `op` b)

-- inOpLs :: (ProductCat k, OpCon' k op con)
--        => (Ok k (con a), Ok k (con b))
--        => Prod k (Prod k (con a) (con b)) (con c)
--        `k` con ((a `op` b) `op` c)
-- inOpLs = inOp' . first  inOp'

{--------------------------------------------------------------------
    Categories
--------------------------------------------------------------------}

class Category (k :: u -> u -> *) where
  type Ok k :: u -> Constraint
  type Ok k = Yes
  id  :: Ok k a => a `k` a
  infixr 9 .
  (.) :: Ok3 k a b c => b `k` c -> a `k` b -> a `k` c
#ifdef DefaultCat
  -- Defaults experiment
  default id :: C.Category k => a `k` a
  id = C.id
  default (.) :: C.Category k => b `k` c -> a `k` b -> a `k` c
  (.) = (C..)
#endif

type CatOk k ok = (Category k, ok ~ Ok k)

infixl 1 <~
infixr 1 ~>
-- | Add post- and pre-processing
(<~) :: (Category k, Ok4 k a b a' b') 
     => (b `k` b') -> (a' `k` a) -> ((a `k` b) -> (a' `k` b'))
(h <~ f) g = h . g . f

-- | Add pre- and post-processing
(~>) :: (Category k, Ok4 k a b a' b') 
     => (a' `k` a) -> (b `k` b') -> ((a `k` b) -> (a' `k` b'))
f ~> h = h <~ f

#if DefaultCat
instance Category (->)
instance Monad m => Category (Kleisli m)
#else
instance Category (->) where
  id  = P.id
  (.) = (P..)

instance Monad m => Category (Kleisli m) where
  id  = pack return
  (.) = inNew2 (<=<)
#endif

{--------------------------------------------------------------------
    Products
--------------------------------------------------------------------}

infixr 3 ***, &&&

-- | Category with product.
class (OpCon (Prod k) (Ok k), Category k) => ProductCat k where
  type Prod k :: u -> u -> u
  -- type Prod k = (:*)
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  dup :: Ok k a => a `k` Prod k a a
  dup = id &&& id
  swapP :: forall a b. Ok2 k a b => Prod k a b `k` Prod k b a
  swapP = exr &&& exl
          <+ inOp @(Prod k) @(Ok k) @a @b
  (***) :: forall a b c d. Ok4 k a b c d 
        => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
  f *** g = f . exl &&& g . exr
            <+ inOp @(Prod k) @(Ok k) @a @b
  (&&&) :: forall a c d. Ok3 k a c d 
        => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)
  f &&& g = (f *** g) . dup
    <+ inOp @(Prod k) @(Ok k) @a @a
    <+ inOp @(Prod k) @(Ok k) @c @d
  first :: forall a a' b. Ok3 k a b a' 
        => (a `k` a') -> (Prod k a b `k` Prod k a' b)
  first = (*** id)
  second :: forall a b b'. Ok3 k a b b' 
         => (b `k` b') -> (Prod k a b `k` Prod k a b')
  second = (id ***)
  lassocP :: forall a b c. Ok3 k a b c
          => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c
  lassocP = second exl &&& (exr . exr)
            <+ inOp   @(Prod k) @(Ok k) @a @b
            <+ inOpR' @(Prod k) @(Ok k) @a @b @c
  rassocP :: forall a b c. Ok3 k a b c
          => Prod k (Prod k a b) c `k` Prod k a (Prod k b c)
  rassocP = (exl . exl) &&& first  exr
            <+ inOp   @(Prod k) @(Ok k)    @b @c
            <+ inOpL' @(Prod k) @(Ok k) @a @b @c
  {-# MINIMAL exl, exr, ((&&&) | ((***), dup)) #-}
#ifdef DefaultCat
  default exl :: A.Arrow k => (a :* b) `k` a
  exl = arr exl
  default exr :: A.Arrow k => (a :* b) `k` b
  exr = arr exr
  default (&&&) :: A.Arrow k => a `k` c -> a `k` d -> a `k` (c :* d)
  (&&&) = (A.&&&)
  -- OOPS. We can't give two default definitions for (&&&).
#endif

-- TODO: find some techniques for prettifying type operators.

type ProdOk k ok = (ProductCat k, ok ~ Ok k)

instance ProductCat (->) where
  type Prod (->) = (:*)
  exl     = fst
  exr     = snd
  (&&&)   = (A.&&&)
  (***)   = (A.***)
  first   = A.first
  second  = A.second
  lassocP = \ (a,(b,c)) -> ((a,b),c)
  rassocP = \ ((a,b),c) -> (a,(b,c))

-- | Apply to both parts of a product
twiceP :: (ProductCat k, Ok k a, Ok k c) 
       => (a `k` c) -> Prod k a a `k` (Prod k c c)
twiceP f = f *** f

-- | Operate on left-associated form
inLassocP :: forall k a b c a' b' c'. (ProductCat k, Ok6 k a b c a' b' c') 
          => Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
          -> Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
inLassocP = rassocP <~ lassocP
              <+ (inOpLR @(Prod k) @(Ok k) @a  @b  @c C.***
                  inOpLR @(Prod k) @(Ok k) @a' @b' @c')

-- | Operate on right-associated form
inRassocP :: forall a b c a' b' c' k.
             (ProductCat k, Ok6 k a b c a' b' c') 
          => Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
          -> Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
inRassocP = lassocP <~ rassocP
              <+ (inOpLR @(Prod k) @(Ok k) @a  @b  @c C.***
                  inOpLR @(Prod k) @(Ok k) @a' @b' @c')

transposeP :: forall k a b c d. (ProductCat k, Ok4 k a b c d)
           => Prod k (Prod k a b) (Prod k c d) `k` Prod k (Prod k a c) (Prod k b d)
transposeP = (exl.exl &&& exl.exr) &&& (exr.exl &&& exr.exr)
  <+ inOp @(Prod k) @(Ok k) @(Prod k a b) @(Prod k c d)
  <+ inOp @(Prod k) @(Ok k) @c @d
  <+ inOp @(Prod k) @(Ok k) @a @b
  <+ inOp @(Prod k) @(Ok k) @b @d
  <+ inOp @(Prod k) @(Ok k) @a @c

-- | Inverse to '(&&&)'
unfork :: forall k a c d. (ProductCat k, Ok3 k a c d) 
       => (a `k` Prod k c d) -> (a `k` c, a `k` d)
unfork f = (exl . f, exr . f)  <+ inOp @(Prod k) @(Ok k) @c @d

instance Monad m => ProductCat (Kleisli m) where
  type Prod (Kleisli m) = (:*)
  exl   = arr exl
  exr   = arr exr
  dup   = arr dup
  (&&&) = inNew2 forkA
  (***) = inNew2 crossA

forkA :: Applicative m => (a -> m c) -> (a -> m d) -> (a -> m (c :* d))
(f `forkA` g) a = liftA2 (,) (f a) (g a)

crossA :: Applicative m => (a -> m c) -> (b -> m d) -> (a :* b -> m (c :* d))
(f `crossA` g) (a,b) = liftA2 (,) (f a) (g b)

{--------------------------------------------------------------------
    Coproducts
--------------------------------------------------------------------}

infixr 2 +++, |||

-- | Category with coproduct.
class (OpCon (Coprod k) (Ok k), Category k) => CoproductCat k where
  type Coprod k :: u -> u -> u
  -- type Coprod k = (:+)
  inl :: Ok2 k a b => a `k` Coprod k a b
  inr :: Ok2 k a b => b `k` Coprod k a b
  jam :: Ok k a => Coprod k a a `k` a
  jam = id ||| id
  swapS :: forall a b. Ok2 k a b => Coprod k a b `k` Coprod k b a
  swapS = inr ||| inl
          <+ inOp @(Coprod k) @(Ok k) @b @a
  (+++) :: forall a b c d. Ok4 k a b c d 
        => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b)
  f +++ g = inl . f ||| inr . g
            <+ inOp @(Coprod k) @(Ok k) @a @b
  (|||) :: forall a c d. Ok3 k a c d 
        => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)
  f ||| g = jam . (f +++ g)
          <+ inOp @(Coprod k) @(Ok k) @a @a
          <+ inOp @(Coprod k) @(Ok k) @c @d
  left  :: forall a a' b. Ok3 k a b a' 
        => (a `k` a') -> (Coprod k a b `k` Coprod k a' b)
  left  = (+++ id)
  right :: forall a b b'. Ok3 k a b b' 
        => (b `k` b') -> (Coprod k a b `k` Coprod k a b')
  right = (id +++)
  lassocS :: forall a b c. Ok3 k a b c
          => Coprod k a (Coprod k b c) `k` Coprod k (Coprod k a b) c
  lassocS = inl.inl ||| (inl.inr ||| inr)
            <+ inOpL' @(Coprod k) @(Ok k) @a @b @c
            <+ inOp   @(Coprod k) @(Ok k)    @b @c
  rassocS :: forall a b c. Ok3 k a b c
          => Coprod k (Coprod k a b) c `k` Coprod k a (Coprod k b c)
  rassocS = (inl ||| inr.inl) ||| inr.inr
            <+ inOpR' @(Coprod k) @(Ok k) @a @b @c
            <+ inOp   @(Coprod k) @(Ok k) @a @b
  {-# MINIMAL inl, inr, ((|||) | ((+++), jam)) #-}

type CoprodOk k ok = (CoproductCat k, ok ~ Ok k)

instance CoproductCat (->) where
  type Coprod (->) = (:+)
  inl   = Left
  inr   = Right
  (|||) = (A.|||)
  (+++) = (A.+++)
  left  = A.left
  right = A.right


-- -- | Operate on left-associated form
-- inLassocP :: forall k a b c a' b' c'.
--              (ProductCat k, Ok6 k a b c a' b' c') 
--           => Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
--           -> Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
-- inLassocP = rassocP <~ lassocP
--               <+ (inOpLR @(Prod k) @(Ok k) @a  @b  @c C.***
--                   inOpLR @(Prod k) @(Ok k) @a' @b' @c')

-- -- | Operate on right-associated form
-- inRassocP :: forall a b c a' b' c' k.
--              (ProductCat k, Ok6 k a b c a' b' c') 
--           => Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
--           -> Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
-- inRassocP = lassocP <~ rassocP
--               <+ (inOpLR @(Prod k) @(Ok k) @a  @b  @c C.***
--                   inOpLR @(Prod k) @(Ok k) @a' @b' @c')


-- | Operate on left-associated form
inLassocS :: forall k a b c a' b' c'. (CoproductCat k, Ok6 k a b c a' b' c') 
          => Coprod k (Coprod k a b) c `k` Coprod k (Coprod k a' b') c'
          -> Coprod k a (Coprod k b c) `k` (Coprod k a' (Coprod k b' c'))
inLassocS = rassocS <~ lassocS
            <+ (inOpLR @(Coprod k) @(Ok k) @a  @b  @c C.***
                inOpLR @(Coprod k) @(Ok k) @a' @b' @c')

-- | Operate on right-associated form
inRassocS :: forall a b c a' b' c' k.
             (CoproductCat k, Ok6 k a b c a' b' c') 
          => Coprod k a (Coprod k b c) `k` (Coprod k a' (Coprod k b' c'))
          -> Coprod k (Coprod k a b) c `k` Coprod k (Coprod k a' b') c'
inRassocS = lassocS <~ rassocS
            <+ (inOpLR @(Coprod k) @(Ok k) @a  @b  @c C.***
                inOpLR @(Coprod k) @(Ok k) @a' @b' @c')

transposeS :: forall k a b c d. (CoproductCat k, Ok4 k a b c d)
           => Coprod k (Coprod k a b) (Coprod k c d) `k` Coprod k (Coprod k a c) (Coprod k b d)
transposeS = (inl.inl ||| inr.inl) ||| (inl.inr ||| inr.inr)
  <+ inOp @(Coprod k) @(Ok k) @(Coprod k a c) @(Coprod k b d)
  <+ inOp @(Coprod k) @(Ok k) @c @d
  <+ inOp @(Coprod k) @(Ok k) @a @b
  <+ inOp @(Coprod k) @(Ok k) @b @d
  <+ inOp @(Coprod k) @(Ok k) @a @c

-- | Inverse to '(|||)'
unjoin :: forall k a c d. (CoproductCat k, Ok3 k a c d) 
       => (Coprod k c d `k` a) -> (c `k` a, d `k` a)
unjoin f = (f . inl, f . inr)  <+ inOp @(Coprod k) @(Ok k) @c @d

{--------------------------------------------------------------------
    Exponentials
--------------------------------------------------------------------}

class ProductCat k => ClosedCat k where
  type Exp k :: u -> u -> u
  apply   :: Ok2 k a b   => Prod k (Exp k a b) a `k` b
  curry   :: Ok3 k a b c => (Prod k a b `k` c) -> (a `k` Exp k b c)
  uncurry :: Ok3 k a b c => (a `k` Exp k b c)  -> (Prod k a b `k` c)

--   apply   :: (Ok2 k a b, p ~ Prod k, e ~ Exp k) => ((a `e` b) `p` a) `k` b

instance ClosedCat (->) where
  type Exp (->) = (->)
  apply (f,a) = f a
  curry       = P.curry
  uncurry     = P.uncurry

#if 0
applyK   ::            Kleisli m (Kleisli m a b :* a) b
curryK   :: Monad m => Kleisli m (a :* b) c -> Kleisli m a (Kleisli m b c)
uncurryK :: Monad m => Kleisli m a (Kleisli m b c) -> Kleisli m (a :* b) c

applyK   = pack (apply . first unpack)
curryK   = inNew $ \ h -> return . pack . curry h
uncurryK = inNew $ \ f -> \ (a,b) -> f a >>= ($ b) . unpack

instance Monad m => ClosedCat (Kleisli m) where
  type Exp (Kleisli m) = Kleisli m
  apply   = applyK
  curry   = curryK
  uncurry = uncurryK
#else
instance Monad m => ClosedCat (Kleisli m) where
  type Exp (Kleisli m) = Kleisli m
  apply   = pack (apply . first unpack)
  curry   = inNew $ \ h -> return . pack . curry h
  uncurry = inNew $ \ f -> \ (a,b) -> f a >>= ($ b) . unpack
#endif

{--------------------------------------------------------------------
    Other
--------------------------------------------------------------------}

class TerminalCat k where
  it :: Ok2 k a () => a `k` Unit

instance TerminalCat (->) where it = const ()

-- | Categories with constant arrows (generalized elements)
class ConstCat k where
  konst :: forall a b. Ok2 k a b => b -> (a `k` b)

instance ConstCat (->) where konst = const

-- class ApplyToCat k where
--   applyTo :: Ok2 k a b => a -> ((a -> b) `k` b)

-- Do I want `Exp k a b` in place of `a -> b`?
-- LMap seems to want ->.

-- class ClosedCat k => ApplyToCat k where
--   applyTo :: Ok2 k a b => a -> (Exp k a b `k` b)

#if 0

class Category k => UnsafeArr k where
  unsafeArr :: Ok2 k a b => (a -> b) -> a `k` b

instance UnsafeArr (->) where
  unsafeArr = A.arr

instance Monad m => UnsafeArr (Kleisli m) where
  unsafeArr = A.arr
  
#endif

{--------------------------------------------------------------------
    Some categories
--------------------------------------------------------------------}

-- Exactly one arrow for each pair of objects.
data U2 (a :: *) (b :: *) = U2

-- Is there a standard name and/or generalization?
-- Seems to be called "indiscrete" or "chaotic"

instance Category U2 where
  id = U2
  U2 . U2 = U2

instance ProductCat U2 where
  type Prod U2 = (:*)
  exl = U2
  exr = U2
  U2 &&& U2 = U2

instance CoproductCat U2 where
  type Coprod U2 = (:+)
  inl = U2
  inr = U2
  U2 ||| U2 = U2

instance ClosedCat U2 where
  type Exp U2 = (->)
  apply = U2
  curry U2 = U2
  uncurry U2 = U2

instance TerminalCat U2 where it = U2

instance ConstCat U2 where konst = const U2

{--------------------------------------------------------------------
    Natural transformations
--------------------------------------------------------------------}

-- ↠, \twoheadrightarrow

data a --> b = NT (forall (t :: *). a t -> b t)

-- instance Newtype (a --> b) where
--   -- Illegal polymorphic type: forall t. a t -> b t
--   type O (a --> b) = forall t. a t -> b t
--   pack h = NT h
--   unpack (NT h) = h

instance Category (-->) where
  id = NT id
  NT g . NT f = NT (g . f)

instance ProductCat (-->) where
  type Prod (-->) = (:*:)
  exl = NT (\ (a :*: _) -> a)
  exr = NT (\ (_ :*: b) -> b)
  NT f &&& NT g = NT (pack . (f &&& g))

instance CoproductCat (-->) where
  type Coprod (-->) = (:+:)
  inl = NT L1
  inr = NT R1
  NT a ||| NT b = NT ((a ||| b) . unpack)

instance ClosedCat (-->) where
  type Exp (-->) = (+->)
  apply = NT (\ (ab :*: a) -> unpack ab a)
  curry   (NT f) = NT (\ a -> pack (\ b -> f (a :*: b)))
  uncurry (NT g) = NT (\ (a :*: b) -> unpack (g a) b)

-- With constraint element types

data NTC con a b = NTC (forall (t :: *). con t => a t -> b t)

instance Category (NTC con) where
  id = NTC id
  NTC g . NTC f = NTC (g . f)

instance ProductCat (NTC con) where
  type Prod (NTC con) = (:*:)
  exl = NTC (\ (a :*: _) -> a)
  exr = NTC (\ (_ :*: b) -> b)
  NTC f &&& NTC g = NTC (pack . (f &&& g))

instance CoproductCat (NTC con) where
  type Coprod (NTC con) = (:+:)
  inl = NTC L1
  inr = NTC R1
  NTC a ||| NTC b = NTC ((a ||| b) . unpack)

instance ClosedCat (NTC con) where
  type Exp (NTC con) = (+->)
  apply = NTC (\ (ab :*: a) -> unpack ab a)
  curry   (NTC f) = NTC (\ a -> pack (\ b -> f (a :*: b)))
  uncurry (NTC g) = NTC (\ (a :*: b) -> unpack (g a) b)

-- An unquantified version

data UT (t :: *) a b = UT (a t -> b t)

instance Category (UT t) where
  id = UT id
  UT g . UT f = UT (g . f)

instance ProductCat (UT t) where
  type Prod (UT t) = (:*:)
  exl = UT (\ (a :*: _) -> a)
  exr = UT (\ (_ :*: b) -> b)
  UT f &&& UT g = UT (pack . (f &&& g))

instance CoproductCat (UT t) where
  type Coprod (UT t) = (:+:)
  inl = UT L1
  inr = UT R1
  UT a ||| UT b = UT ((a ||| b) . unpack)

instance ClosedCat (UT t) where
  type Exp (UT t) = (+->)
  apply = UT (\ (ab :*: a) -> unpack ab a)
  curry   (UT f) = UT (\ a -> pack (\ b -> f (a :*: b)))
  uncurry (UT g) = UT (\ (a :*: b) -> unpack (g a) b)

-- With constraints

data UTC con (t :: *) a b = UTC (con t => a t -> b t)

instance Category (UTC con t) where
  id = UTC id
  UTC g . UTC f = UTC (g . f)

instance ProductCat (UTC con t) where
  type Prod (UTC con t) = (:*:)
  exl = UTC (\ (a :*: _) -> a)
  exr = UTC (\ (_ :*: b) -> b)
  UTC f &&& UTC g = UTC (pack . (f &&& g))

instance CoproductCat (UTC con t) where
  type Coprod (UTC con t) = (:+:)
  inl = UTC L1
  inr = UTC R1
  UTC a ||| UTC b = UTC ((a ||| b) . unpack)

instance ClosedCat (UTC con t) where
  type Exp (UTC con t) = (+->)
  apply = UTC (\ (ab :*: a) -> unpack ab a)
  curry   (UTC f) = UTC (\ a -> pack (\ b -> f (a :*: b)))
  uncurry (UTC g) = UTC (\ (a :*: b) -> unpack (g a) b)

{--------------------------------------------------------------------
    Entailment
--------------------------------------------------------------------}

-- Copied from Data.Constraint:

-- instance Category (|-) where
--   id  = refl
--   (.) = trans

instance Category (|-) where
  id = Sub Dict
  g . f = Sub $ Dict <+ g <+ f

#if 0
instance ProductCat (|-) where
  type Prod (|-) = (&&)
  exl = weaken1 . unconj
  exr = weaken2 . unconj
  dup = conj . contract
  f &&& g = conj . (f C.&&& g)
  f *** g = conj . (f C.*** g) . unconj
#else
instance ProductCat (|-) where
  type Prod (|-) = (&&)
  exl = Sub Dict
  exr = Sub Dict
  dup = Sub Dict
  f &&& g = Sub $ Dict <+ f <+ g
  f *** g = Sub $ Dict <+ f <+ g
#endif

#if 0
class Entails a b where entails :: a |- b

instance ClosedCat (|-) where
  type Exp (|-) = Entails
--   apply :: forall a b. Entails a b && a |- b
--   apply = Sub Dict <+ (entails :: a |- b)

  curry   :: (a && b |- c) -> (a |- Entails b c)
  curry abc = Sub Dict 

--   curry   :: (a && b |- c) -> (a |- Exp (|-) b c)
#endif

{--------------------------------------------------------------------
    Memo tries
--------------------------------------------------------------------}

instance Category (:->:) where
  type Ok (:->:) = HasTrie
  id = idTrie
  (.) = (@.@)

instance ProductCat (:->:) where
  type Prod (:->:) = (:*)
  exl   = trie exl
  exr   = trie exr
  (&&&) = inTrie2 (&&&)

instance CoproductCat (:->:) where
  type Coprod (:->:) = (:+)
  inl   = trie inl
  inr   = trie inr
  (|||) = inTrie2 (|||)

instance OpCon (:*) HasTrie where inOp = Sub Dict
instance OpCon (:+) HasTrie where inOp = Sub Dict

#if 0
instance OpCon (:->:) HasTrie where inOp = Sub Dict

instance ClosedCat (:->:) where
  type Exp (:->:) = (:->:)
  apply :: forall a b. Ok2 (:->:) a b => Exp (:->:) a b :* a :->: b
  apply = trie (apply . first untrie)
    <+ inOp @(Exp (:->:)) @(Ok (:->:)) @a @b
  curry = unpack
  uncurry = pack
  -- apply = (pack.trie) (\ (Memod t, a) -> untrie t a)
#else

-- instance ClosedCat (:->:) where
--   type Exp (:->:) = (->)
--   apply :: forall a b. C2 HasTrie a b => (a -> b) :* a :->: b

#endif

-- -- Idea: Use (->) for Exp (:->:)

-- curry :: ((a :* b) :->: c) -> (a :-> (b -> c))
-- uncurry :: (a :-> (b -> c)) -> ((a :* b) :->: c)

#if 1

{--------------------------------------------------------------------
    Optional memoization
--------------------------------------------------------------------}

-- Some operations we can't or don't want to memoize, e.g., apply, exl, exr,
-- inl, inr.

infixr 1 :->?
data a :->? b = Fun (a -> b) | Trie (a :->: b)

untrie' :: HasTrie a => (a :->? b) -> (a -> b)
untrie' (Fun  f) = f
untrie' (Trie t) = untrie t

trie' :: HasTrie a => (a -> b) -> (a :->? b)
trie' = Trie . trie

-- | Apply a unary function inside of a trie
inTrie' :: (HasTrie a, HasTrie c)
        => ((a  ->  b) -> (c  ->  d))
        -> ((a :->? b) -> (c :->? d))
inTrie' = trie' <~ untrie'

-- | Apply a binary function inside of a trie
inTrie2' :: (HasTrie a, HasTrie c, HasTrie e) 
         => ((a  ->  b) -> (c  ->  d) -> (e  ->  f))
         -> ((a :->? b) -> (c :->? d) -> (e :->? f))
inTrie2' = inTrie' <~ untrie'

instance Category (:->?) where
  type Ok (:->?) = HasTrie
  id = Fun id
  (.) = inTrie2' (.)

--   Fun g . Fun f = Fun (g . f)
--   g . f = trie' (untrie' g . untrie' f)

instance ProductCat (:->?) where
  type Prod (:->?) = (:*)
  exl = Fun exl
  exr = Fun exr
  (&&&) = inTrie2' (&&&)

--   f &&& g = trie' (untrie' f &&& untrie' g)

instance ClosedCat (:->?) where
  type Exp (:->?) = (->)
  apply = Fun apply
  curry f = Fun (curry (untrie' f))
  uncurry g = Fun (uncurry (untrie' g))

--   apply :: C2 HasTrie a b => (a -> b) :* a :->? b
--   curry :: C3 HasTrie a b c => (a :* b :->? c) -> (a :->? (b -> c))
--   uncurry :: C3 HasTrie a b c => (a :->? (b -> c)) -> (a :* b :->? c)

#endif

{--------------------------------------------------------------------
    Free vector spaces
--------------------------------------------------------------------}

newtype LMapF a b s = LMapF (a (b s))

-- Could I simply use a :.: b instead?

-- instance Category LMapF where
--   id = 
