{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Indexed sets of morphisms

module ConCat.Choice where

import Prelude hiding (id,(.),curry,uncurry,const)
import qualified Prelude as P
import GHC.Types (Constraint)
import Control.Applicative (liftA2)
#ifdef VectorSized
import GHC.TypeLits (KnownNat)
#endif

import Data.Constraint (Dict(..),(:-)(..))  -- temp
import Control.Newtype (Newtype(..))
import Data.Key (Zip)
import Data.Pointed (Pointed)
import Data.Distributive (Distributive)
import Data.Functor.Rep (Representable)

import ConCat.Misc ((:*),oops,inNew,inNew2)
import ConCat.Category
import ConCat.AltCat (toCcc,unCcc)

-- | Nondeterminism category. Like a set of morphisms all of the same type, but
-- represented as a function whose range is that set. The function's domain is
-- existentially hidden.
newtype Choice con a b = Choice (OptArg con (a -> b))

instance Newtype (Choice con a b) where
  type O (Choice con a b) = OptArg con (a -> b)
  pack o = Choice o
  unpack (Choice o) = o

-- Equivalently,
-- 
-- data Choice con a b = forall p. con p => Choice (p -> a -> b)

onChoice :: forall con a b q. con () =>
            (forall p. con p => (p -> a -> b) -> q) -> Choice con a b -> q
onChoice h (Choice o) = onOptArg h o
-- onChoice h (Choice o) = onOptArg' (h ()) h
{-# INLINE onChoice #-}

-- | Deterministic (trivially nondeterministic) arrow
exactly :: con () => (a -> b) -> Choice con a b
exactly f = Choice (NoArg f)  -- or pure, requiring CartCon con
{-# INLINE exactly #-}

#if 0

-- | Generate any value of type @p@.
chooseC :: forall con p a b. (CartCon con, con p)
        => Choice con (p :* a) b -> Choice con a b
chooseC (Choice (NoArg (f :: p :* a -> b))) =
  Choice @con (Arg (curry f))
chooseC (Choice (Arg (f :: q -> p :* a -> b))) =
  Choice @con (Arg (uncurry (curry . f)))
    <+ inOp @(:*) @(Sat con) @q @p
{-# INLINE chooseC #-}

-- TODO: use onOptArg or onOptArg'

--           Choice f  :: Choice con (p :* a) b
--                  f  :: q -> p :* a -> b
--          curry . f  :: q -> p -> a -> b
-- uncurry (curry . f) :: q :* p -> a -> b

-- Equivalently, \ (q,p) a -> f q (p,a)

-- | Generate any value of type @p@.
choose :: forall con p a b. (CartCon con, con p)
       => (p -> a -> b) -> (a -> b)
choose f = unCcc (chooseC @con (toCcc (uncurry f)))
{-# INLINE choose #-}

#else

-- This version is a bit simpler, but we're getting a plugin failure to do with
-- an unknown p type.

-- | Generate any value of type @p@.
chooseC :: forall con p a b. (CartCon con, con p)
         => Choice con p (a -> b) -> Choice con a b
chooseC (Choice (NoArg (f :: p -> a -> b))) =
  Choice @con (Arg f)
chooseC (Choice (Arg (f :: q -> p -> a -> b))) =
  Choice @con (Arg (uncurry f))
    <+ inOp @(:*) @(Sat con) @q @p
{-# INLINE chooseC #-}

#if 0
-- | Generate any value of type @p@.
choose :: forall con p a b. (CartCon con, con p)
        => (p -> a -> b) -> (a -> b)
choose f = unCcc (chooseC @con (toCcc f))
{-# INLINE choose #-}

-- | Generate any value of type @p@.
chooseC' :: forall con p a. (CartCon con, con p)
          => (p -> a) -> Choice con () a
chooseC' f = Choice @con (Arg (const . f))
{-# INLINE chooseC' #-}

-- | Generate any value of type @p@.
choose' :: forall con p a. (CartCon con, con p)
         => (p -> a) -> a
-- choose' f = unCcc (chooseC' @con f) ()
choose' f = choose @con (const . f) ()
{-# INLINE choose' #-}

-- Maybe I want set-valued functions instead of sets of functions.
-- Use a -> p -> b instead of p -> a -> b.

#else

-- | Generate any value of type @p@.
choose :: forall con p a. (CartCon con, con p)
       => (p -> a) -> a
choose = unCcc (Choice @con (Arg (flip ($))))
{-# INLINE choose #-}

--      ($) :: (p -> a) -> p -> a
-- flip ($) :: p -> (p -> a) -> a

#endif

#endif

{--------------------------------------------------------------------
    Category class instances
--------------------------------------------------------------------}

op1C :: forall con a b c d. CartCon con
     => ((a -> b) -> (c -> d))
     -> (Choice con a b -> Choice con c d)
op1C = inNew . fmap'
-- op1C = inNew . fmap
-- op1C = inNew . fmapOpt  -- Experiment
{-# INLINE op1C #-}

op2C :: forall con a b c d e f. CartCon con
     => ((a -> b) -> (c -> d) -> (e -> f))
     -> (Choice con a b -> Choice con c d -> Choice con e f)
op2C = inNew2 . liftA2'
-- op2C = inNew2 . liftA2
-- op2C = inNew2 . liftA2Opt  -- Experiment
{-# INLINE op2C #-}

-- fmap' and liftA2' are class-op-inlining synonyms for fmap and liftA2, defined
-- in ConCat.Category and re-exported from ConCat.AltCat. When I use fmap
-- and liftA2, a rule in AltCat replaces fmap with fmapC, breaking the
-- inlining of fmap in the OptArg instance. As a result, we don't get to
-- eliminate a case that case-binds a variable we need to (but cannot) inline.
-- Look for a better alternative. See 2017-10-20 notes.

instance CartCon con => Category (Choice con) where
  -- type Ok (Choice con) = Ok (->) -- Yes1
  id = exactly id
  (.) = op2C (.)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance CartCon con => ProductCat (Choice con) where
  exl = exactly exl
  exr = exactly exr
  (&&&) = op2C (&&&)
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

instance CartCon con => CoproductCat (Choice con) where
  inl = exactly inl
  inr = exactly inr
  (|||) = op2C (|||)
  {-# INLINE (|||) #-}

instance CartCon con => DistribCat (Choice con) where
  distl = exactly distl
  distr = exactly distr
  {-# INLINE distl #-}
  {-# INLINE distr #-}

instance CartCon con => ClosedCat (Choice con) where
  apply = exactly apply
  curry = op1C curry
  uncurry = op1C uncurry
  {-# INLINE apply #-}
  {-# INLINE curry #-}
  {-# INLINE uncurry #-}

instance CartCon con => TerminalCat (Choice con)

instance CartCon con => ConstCat (Choice con) b where
  const b = exactly (const b)

instance CartCon con => BoolCat (Choice con) where
  notC = exactly notC
  andC = exactly andC
  orC  = exactly orC
  xorC = exactly xorC

instance (Eq a, CartCon con) => EqCat (Choice con) a where
  equal    = exactly equal
  notEqual = exactly notEqual

instance (Ord a, CartCon con) => OrdCat (Choice con) a where
  lessThan           = exactly lessThan
  greaterThan        = exactly greaterThan
  lessThanOrEqual    = exactly lessThanOrEqual
  greaterThanOrEqual = exactly greaterThanOrEqual

instance (Ord a, CartCon con) => MinMaxCat (Choice con) a where
  minC = exactly minC
  maxC = exactly maxC

instance (Enum a, CartCon con) => EnumCat (Choice con) a where
  succC = exactly succC
  predC = exactly predC

instance (Num a, CartCon con) => NumCat (Choice con) a where
  addC    = exactly addC
  mulC    = exactly mulC
  negateC = exactly negateC
  powIC   = exactly powIC

instance (Integral a, con ()) => IntegralCat (Choice con) a where
  divC = exactly divC
  modC = exactly modC

instance (Fractional a, con ()) => FractionalCat (Choice con) a where
  recipC  = exactly recipC
  divideC = exactly divideC

instance (Floating a, con ()) => FloatingCat (Choice con) a where
  expC = exactly expC
  cosC = exactly cosC
  sinC = exactly sinC
  logC = exactly logC

instance (Integral b, RealFrac a, con ()) => RealFracCat (Choice con) a b where
  floorC    = exactly floorC
  ceilingC  = exactly ceilingC
  truncateC = exactly truncateC

instance (Integral a, Num b, con ()) => FromIntegralCat (Choice con) a b where
  fromIntegralC = exactly fromIntegralC

instance (con ()) => BottomCat (Choice con) a b where
  bottomC = exactly bottomC

instance CartCon con => IfCat (Choice con) a where
  ifC = exactly ifC

instance con () => UnknownCat (Choice con) a b where
  unknownC = exactly unknownC

instance (RepCat (->) a r, con ()) => RepCat (Choice con) a r where
  reprC = exactly reprC
  abstC = exactly abstC

instance OkFunctor (Choice con) h where okFunctor = Entail (Sub Dict)

instance (CartCon con, Functor h) => FunctorCat (Choice con) h where
  fmapC = op1C fmapC
  unzipC = exactly unzipC

-- Question: should fmap replicate degrees of freedom or share them?

instance (Zip h, CartCon con) => ZipCat (Choice con) h where
  zipC = exactly zipC

-- TODO: ZapCat instance? I don't think so, but we'll see.

instance (Pointed h, CartCon con) => PointedCat (Choice con) h where
  pointC = exactly pointC

instance (Foldable h, CartCon con) => SumCat (Choice con) h where
  sumC = exactly sumC

instance (FunctorCat k h, CartCon con) => Strong (Choice con) h where
  strength = exactly strength

instance (Distributive g, Functor f, CartCon con)
      => DistributiveCat (Choice con) g f where
  distributeC = exactly distributeC

instance (Representable f, CartCon con) => RepresentableCat (Choice con) f where
  tabulateC = exactly tabulateC
  indexC    = exactly indexC

{--------------------------------------------------------------------
    Maybe move somewhere else
--------------------------------------------------------------------}

-- A function from a constrained, existentially hidden parameter. Optimizes for
-- the parameter being () in order to avoid accumulating products of units.
data OptArg con z = NoArg z | forall p. con p => Arg (p -> z)

-- Equivalently,

-- data OptArg :: (* -> Constraint) -> * -> * where
--   NoArg ::                z  -> OptArg con z 
--   Arg   :: con p => (p -> z) -> OptArg con z

onOptArg :: forall con z q. con ()
         => (forall p. con p => (p -> z) -> q) -> OptArg con z -> q

onOptArg h (NoArg z) = h (\ () -> z)
onOptArg h (Arg f)   = h f

-- onOptArg h o = h (case o of NoArg z -> \ () -> z
--                             Arg f   -> f)

{-# INLINE onOptArg #-}

onOptArg' :: forall con z q. con ()
          => (z -> q)
          -> (forall p. con p => (p -> z) -> q)
          -> OptArg con z -> q
onOptArg' g _ (NoArg z) = g z
onOptArg' _ h (Arg f)   = h f
{-# INLINE onOptArg' #-}

type CartCon con = (con (), OpCon (:*) (Sat con))

#if 1

instance CartCon con => Functor (OptArg con) where
  fmap f (NoArg u) = NoArg (f u)
  fmap f (  Arg g) = Arg (f . g)
  {-# INLINE fmap #-}

instance CartCon con => Applicative (OptArg con) where
  pure = NoArg
  NoArg f <*> NoArg a = NoArg (f a)
  NoArg f <*> Arg as = Arg (f . as)
  Arg (g :: q -> a -> b) <*> NoArg a = Arg (flip g a)
  Arg (g :: q -> a -> b) <*> Arg (f :: p -> a) =
    Arg (\ (p,q) -> g q (f p)) <+ inOp @(:*) @(Sat con) @p @q
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

#else

-- Experiment
fmapOpt :: (a -> b) -> OptArg con a -> OptArg con b
fmapOpt f (NoArg u) = NoArg (f u)
fmapOpt f (  Arg g) = Arg (f . g)
{-# INLINE fmapOpt #-}

liftA2Opt :: forall con a b c. CartCon con =>
     (a -> b -> c) -> OptArg con a -> OptArg con b -> OptArg con c
liftA2Opt h (NoArg a) (NoArg b) = NoArg (h a b)
liftA2Opt h (NoArg a) (Arg bs) = Arg (\ p -> h a (bs p))
liftA2Opt h (Arg as) (NoArg b) = Arg (\ p -> h (as p) b)
liftA2Opt h (Arg as) (NoArg b) = Arg (\ p -> h (as p) b)
liftA2Opt h (Arg (g :: q -> a)) (Arg (f :: p -> b)) =
  Arg (\ (p,q) -> h (g q) (f p)) <+ inOp @(:*) @(Sat con) @p @q
{-# INLINE liftA2Opt #-}

#endif

-- Other classes

-- instance (Monoid a, CartCon con) => Monoid (OptArg con a) where
--   mempty = NoArg mempty
--   mappend = liftA2 mappend
