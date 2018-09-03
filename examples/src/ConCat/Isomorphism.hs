{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}

-- | Category of Isomorphisms.

module ConCat.Isomorphism where

import Prelude hiding (id, (.), const, curry,uncurry)  -- Coming from ConCat.AltCat.

import Data.Functor.Rep (Representable(..))
-- import Control.Applicative (liftA2)
-- import Data.Coerce (Coercible,coerce)
import Control.Newtype.Generics
import qualified GHC.Generics as G
import Data.Constraint (Dict(..),(:-)(..))

import ConCat.Misc ((:+),(:*),(:=>))
import ConCat.AltCat
import qualified ConCat.Category
import qualified ConCat.Rep as R

infix 0 :<->
data Iso k a b = (a `k` b) :<-> (b `k` a)

-- Helpful?
instance R.HasRep (Iso k a b) where
  type Rep (Iso k a b) = (a `k` b) :* (b `k` a)
  abst (f,f') = f :<-> f'
  repr (f :<-> f') = (f,f')

inv :: Iso k a b -> Iso k b a
inv (f :<-> f') = f' :<-> f
{-# INLINE inv #-}

-- | Form an ivolution from a _self-inverse_ arrow.
involution :: (a `k` a) -> Iso k a a
involution f = f :<-> f

instance Category k => Category (Iso k) where
  type Ok (Iso k) = Ok k
  id = id :<-> id
  (g :<-> g') . (f :<-> f') = (g . f) :<-> (f' . g')
  {- INLINE id #-}
  {- INLINE (.) #-}

instance AssociativePCat k => AssociativePCat (Iso k) where
  lassocP = lassocP :<-> rassocP
  rassocP = rassocP :<-> lassocP
  {- INLINE lassocP #-}
  {- INLINE rassocP #-}

instance BraidedPCat k => BraidedPCat (Iso k) where
  swapP = swapP :<-> swapP
  {-# INLINE swapP #-}

instance MonoidalPCat k => MonoidalPCat (Iso k) where
  (f :<-> f') *** (g :<-> g') = (f *** g) :<-> (f' *** g')
  {- INLINE (***) #-}

instance AssociativeSCat k => AssociativeSCat (Iso k) where
  lassocS = lassocS :<-> rassocS
  rassocS = rassocS :<-> lassocS
  {- INLINE lassocS #-}
  {- INLINE rassocS #-}

instance MonoidalSCat k => MonoidalSCat (Iso k) where
  (f :<-> f') +++ (g :<-> g') = (f +++ g) :<-> (f' +++ g')
  {- INLINE (+++) #-}

instance BraidedSCat k => BraidedSCat (Iso k) where
  swapS = swapS :<-> swapS
  {-# INLINE swapS #-}

instance UnitCat k => UnitCat (Iso k) where
  lunit   = lunit   :<-> lcounit
  runit   = runit   :<-> rcounit
  lcounit = lcounit :<-> lunit
  rcounit = rcounit :<-> runit
  {-# INLINE lunit #-}
  {-# INLINE runit #-}
  {-# INLINE lcounit #-}
  {-# INLINE rcounit #-}

-- instance OkFunctor k h => OkFunctor (Iso k) h where okFunctor = Entail (Sub Dict)

instance OkFunctor k h => OkFunctor (Iso k) h where
  okFunctor :: forall a. Ok' (Iso k) a |- Ok' (Iso k) (h a)
  okFunctor = Entail (Sub (Dict <+ okFunctor @k @h @a))
  {-# INLINE okFunctor #-}

instance (FunctorCat k h, ZipCat k h) => FunctorCat (Iso k) h where
  fmapC (f :<-> f') = fmapC f :<-> fmapC f'
  unzipC = unzipC :<-> zipC
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

instance (FunctorCat k h, ZipCat k h) => ZipCat (Iso k) h where
  zipC = zipC :<-> unzipC
  {-# INLINE zipC #-}

-- pure'
-- liftA2'

isoFwd :: Iso k a b -> (a `k` b)
isoFwd (f :<-> _) = f

isoRev :: Iso k a b -> (b `k` a)
isoRev (_ :<-> f') = f'

infix 0 <->
type (<->) = Iso (->)

-- | Apply one isomorphism via another
via :: (Category k, Ok2 k a b) => Iso k b b -> Iso k a b -> Iso k a a
(g :<-> g') `via` (ab :<-> ba) = ba . g . ab :<-> ba . g' . ab
{-# INLINE via #-}

-- Old notation
pattern Iso :: (a `k` b) -> (b `k` a) -> Iso k a b
pattern Iso f f' = f :<-> f'

newIso :: Newtype a => a <-> O a
newIso = unpack :<-> pack
{-# INLINE newIso #-}

hasrepIso :: R.HasRep a => a <-> R.Rep a
hasrepIso = R.repr :<-> R.abst
{-# INLINE hasrepIso #-}

repIso :: Representable f => f a <-> (Rep f -> a)
repIso = index :<-> tabulate
{-# INLINE repIso #-}

reindex :: (Representable f, Representable g) => (Rep g <-> Rep f) -> (f <--> g)
reindex h = inv repIso . dom h . repIso
{-# INLINE reindex #-}

#if 0

h  :: Rep g <-> Rep f

repIso     :: f a          <-> (Rep f -> a)
dom h      :: (Rep f -> a) <-> (Rep g -> a)
inv repIso :: (Rep g -> a) <-> g a

#endif

reindexId :: forall f g. (Representable f, Representable g, Rep f ~ Rep g) => (f <--> g)
reindexId = -- reindex id
            -- inv repIso . dom id . repIso
            -- inv repIso . id . repIso
            inv repIso . repIso

-- coerceIso :: Coercible a b => a <-> b
-- coerceIso = coerce :<-> coerce

coerceIso :: (CoerceCat k a b, CoerceCat k b a) => Iso k a b
coerceIso = coerceC :<-> coerceC

genericIso :: G.Generic a => (a <-> G.Rep a x)
genericIso = G.from :<-> G.to

generic1Iso :: G.Generic1 f => (f <--> G.Rep1 f)
generic1Iso = G.from1 :<-> G.to1

{--------------------------------------------------------------------
    Experiment
--------------------------------------------------------------------}

infixr 8 ^^^
class (Category k, OkExp k) => Closed k where
  (^^^) :: Ok4 k a b c d => (d `k` c) -> (a `k` b) -> ((c :=> a) `k` (d :=> b))

dom :: (Closed k, Ok3 k c a d) => (d `k` c) -> ((c :=> a) `k` (d :=> a))
dom f = f ^^^ id

cod :: (Closed k, Ok3 k c a b) => (a `k` b) -> ((c :=> a) `k` (c :=> b))
cod g = id ^^^ g

foo1, foo2 :: forall k a b c d a' c'.
              (Closed k, Ok k c, Ok k a, Ok k d, Ok k c', Ok k b, Ok k a')
           => (d `k` c') -> (c' `k` c) -> (a `k` a') -> (a' `k` b)
           -> ((c :=> a) `k` (d :=> b))
foo1 f g h k = (f ^^^ k) . (g ^^^ h)
             <+ okExp @k @c  @a
             <+ okExp @k @c' @a'
             <+ okExp @k @d  @b
foo2 f g h k = (g . f) ^^^ (k . h)

-- {-# RULES
-- "(^^^)/(.)" forall f g h k. (f ^^^ k) . (g ^^^ h) = (g . f) ^^^ (k . h)
-- #-}

instance Closed (->) where
  (f ^^^ h) g = h . g . f

instance Closed k => Closed (Iso k) where
  (f :<-> f') ^^^ (h :<-> h') = (f ^^^ h) :<-> (f' ^^^ h')

#if 0

p  :: d `k` c
p' :: c `k` d

q  :: a `k` b
q' :: b `k` a

p  ^^^ q  :: (c :=> a) `k` (d :=> b)
p' ^^^ q' :: (d :=> b) `k` (c :=> a)

#endif

{--------------------------------------------------------------------
    Generic isomorphism-based homomorphisms
--------------------------------------------------------------------}

-- | Natural isomorphism
infix 0 <-->
type f <--> g = forall a. f a <-> g a

fmapIso :: Functor f => (f <--> g) -> (a -> b) -> (g a -> g b)
fmapIso fg h = isoFwd fg . fmap h . isoRev fg

-- Don't pattern match fg, since we need two type instantiations.
-- For instance, the following doesn't type-check:
-- 
--   fmapIso (fg :<-> gf) h = fg . fmap h . gf

pureIso :: Applicative f => (f <--> g) -> a -> g a
pureIso fg a = isoFwd fg (pure a)

appIso :: Applicative f => (f <--> g) -> g (a -> b) -> g a -> g b
appIso fg hs xs = isoFwd fg (isoRev fg hs <*> isoRev fg xs)

memptyIso :: Monoid a => (a <-> b) -> b
memptyIso (ab :<-> _) = ab mempty

mappendIso :: Monoid a => (a <-> b) -> (b -> b -> b)
mappendIso (ab :<-> ba) b b' = ab (ba b `mappend` ba b')

-- mappendIso (ab :<-> ba) (ab a) (ab a') = ab (a `mappend` a')

joinIso :: (MCoproductCat k, Ok3 k a c d) 
        => (c `k` a) :* (d `k` a) <-> ((c :+ d) `k` a)
joinIso = join :<-> unjoin

forkIso :: (MProductCat k, Ok3 k a c d)
        => (a `k` c) :* (a `k` d) <-> (a `k` (c :* d))
forkIso = fork :<-> unfork

curryIso :: (ClosedCat k, Ok3 k a b c)
         => ((a :* b) `k` c) <-> (a `k` (b -> c))
curryIso = curry :<-> uncurry

