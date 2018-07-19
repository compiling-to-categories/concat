{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

-- | Category of Isomorphisms.

module ConCat.Isomorphism where

import Prelude hiding (id, (.), const)  -- Coming from ConCat.AltCat.

import ConCat.Misc ((:*))
import ConCat.AltCat
import qualified ConCat.Category
import ConCat.Rep

infix 0 :<->
data Iso k a b = (a `k` b) :<-> (b `k` a)

-- Helpful?
instance HasRep (Iso k a b) where
  type Rep (Iso k a b) = (a `k` b) :* (b `k` a)
  abst (f,f') = f :<-> f'
  repr (f :<-> f') = (f,f')

inverse :: Iso k a b -> Iso k b a
inverse (f :<-> f') = f' :<-> f
{-# INLINE inverse #-}

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

isoFwd :: Iso k a b -> (a `k` b)
isoFwd (f :<-> _) = f

isoRev :: Iso k a b -> (b `k` a)
isoRev (_ :<-> f') = f'

infix 0 <->
type (<->) = Iso (->)

-- Old notation
pattern Iso :: (a `k` b) -> (b `k` a) -> Iso k a b
pattern Iso f f' = f :<-> f'

{--------------------------------------------------------------------
    Experiment
--------------------------------------------------------------------}

infixr 8 ^^^
class (Category k, OkExp k) => MonoidalECat k where
  (^^^) :: Ok4 k a b a' b' => (a' `k` a) -> (b `k` b') -> ((a -> b) `k` (a' -> b'))

dom :: (MonoidalECat k, Ok3 k a b a') => (a' `k` a) -> ((a -> b) `k` (a' -> b))
dom f = f ^^^ id

cod :: (MonoidalECat k, Ok3 k a b b') => (b `k` b') -> ((a -> b) `k` (a -> b'))
cod g = id ^^^ g

foo1, foo2 :: forall k a a' a'' b b' b''. (MonoidalECat k, Ok6 k a a' a'' b b' b'')
           => (a'' `k` a') -> (a' `k` a) -> (b `k` b') -> (b' `k` b'')
           -> (a -> b) `k` (a'' -> b'')
foo1 f g h k = (f ^^^ k) . (g ^^^ h)
             <+ okExp @k @a   @b
             <+ okExp @k @a'  @b'
             <+ okExp @k @a'' @b''
foo2 f g h k = (g . f) ^^^ (k . h)

-- {-# RULES
-- "(^^^)/(.)" forall f g h k. (f ^^^ k) . (g ^^^ h) = (g . f) ^^^ (k . h)
-- #-}

instance MonoidalECat (->) where
  (p ^^^ q) f = q . f . p

instance MonoidalECat k => MonoidalECat (Iso k) where
  (p :<-> p') ^^^ (q :<-> q') = (p ^^^ q) :<-> (p' ^^^ q')

#if 0

p  :: a' `k` a
p' :: a `k` a'

q  :: b `k` b'
q' :: b' `k` b

p  ^^^ q  :: (a  -> b) `k` (a' -> b')
p' ^^^ q' :: (a' -> b') `k` (a -> b)

#endif
