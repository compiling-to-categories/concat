{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Various functions to ease syntax construction from the plugin

module ConCat.Translators where

import Prelude hiding (id,(.),curry,uncurry,const,unzip,zip,zipWith)
-- import qualified Prelude as P
-- import GHC.Exts (inline)

import ConCat.Misc ((:*),result)
import ConCat.AltCat

-- I could use this simpler style to simplify the plugin, e.g.,

appT :: forall a b c. (a -> b -> c) -> (a -> b) -> (a -> c)
appT f g = apply . (f &&& g)
{-# INLINE appT #-}

-- The plugin would then turn `\ x -> U V` into `appT (\ x -> U) (\ x -> V)`.
-- Or leave the `toCcc'` call in the plugin for separation of concerns.

casePairTopT :: forall b c d. b :* c -> (b -> c -> d) -> d
casePairTopT bc g = uncurryC g bc
{-# INLINE casePairTopT #-}

casePairT :: forall a b c d. (a -> b :* c) -> (a -> b -> c -> d) -> (a -> d)
casePairT f g = uncurryC (result uncurryC g) . (id &&& f)
{-# INLINE casePairT #-}

uncurryC :: (a -> b -> c) -> (a :* b -> c)
uncurryC f w = f (exl w) (exr w)
{-# INLINE uncurryC #-}

-- Unused a
casePairQT :: forall a b c d. (a -> b :* c) -> (b -> c -> d) -> (a -> d)
casePairQT f g = uncurryC g . f
{-# INLINE casePairQT #-}

-- Unused c
casePairLT :: forall a b c d. (a -> b :* c) -> (a -> b -> d) -> (a -> d)
casePairLT f g = uncurryC g . (id &&& exl . f)
{-# INLINE casePairLT #-}

-- Unused b
casePairRT :: forall a b c d. (a -> b :* c) -> (a -> c -> d) -> (a -> d)
casePairRT f g = uncurryC g . (id &&& exr . f)
{-# INLINE casePairRT #-}

-- TODO: given examples of casePairLT and casePairRT, try using the general
-- casePairT instead, and see how well GHC optimizes it. And/or dig up the
-- journal notes I made when I chose to make these special cases.

-- One drawback of using these function-only definitions is that the plugin
-- cannot first check whether the target category has the required properties,
-- such as `ClosedCat`.

-- For `\ x -> fmap U`
fmapTrans1 :: forall k a b c h. (ClosedCat k, Strong k h, Ok3 k a b c)
           => (a `k` (b -> c)) -> (a `k` (h b -> h c))
fmapTrans1 g = curry (fmapTrans (g . exl) exr)
               <+ okProd @k @a @(h b)
               <+ okFunctor @k @h @b
               <+ okFunctor @k @h @c
               <+ okExp @k @b @c

--                                exl       :: a :* h b `k` a
--                                     exr  :: a :* h b `k` h b
--                   (\ a -> U)             :: a `k` (b -> c)
--                   (\ a -> U) . exl       :: (a :* h b) `k` (b -> c)
--        fmapTrans ((\ a -> U) . exl) exr  :: (a :* h b) `k` h c
-- curry (fmapTrans ((\ a -> U) . exl) exr) :: a `k` (h b -> h c)


-- letT :: (p -> a -> b) -> (p -> a) -> (p -> b)
-- letT h f = P.uncurry h . (id &&& f)
-- -- letT h f p = (h p) (f p)

-- fmap musings to be sorted out.

fmapTrans :: forall k a b c h. (ClosedCat k, Strong k h, Ok3 k a b c)
          => (a `k` (b -> c)) -> (a `k` h b) -> (a `k` h c)
fmapTrans f g = fmapC (uncurry f) . strength . (id &&& g)
                <+ okFunctor @k @h @(a :* b)
                <+ okProd @k @a @(h b)
                <+ okFunctor @k @h @c
                <+ okFunctor @k @h @b
                <+ okProd @k @a @b

#if 0
-- Types:

f :: a `k` (b -> c)
g :: a `k` h b

strength :: (a :* h b) `k` h (a :* b)

       uncurry f  :: a :* b `k` c
fmapC (uncurry f) :: h (a :* b) `k` h c

                                id &&& g  :: a `k` (a :* h b)
                    strength . (id &&& g) :: a `k` h (a :* b)
fmapC (uncurry f) . strength . (id &&& g) :: a `k` h c

#endif

-- TODO: Maybe use the following function-only definition instead, and wrap
-- toCcc' around it in the plugin.

fmapTrans' :: Functor h => (a -> (b -> c)) -> (a -> h b) -> (a -> h c)
fmapTrans' f g = fmapC (uncurry f) . strength . (id &&& g)

-- To make it easier yet on the plugin, move the `toCcc'` call into `fmapTrans`:

fmapTrans'' :: Functor h => (a -> (b -> c)) -> (a -> h b) -> (a `k` h c)
fmapTrans'' f g = toCcc' (fmapC (uncurry f) . strength . (id &&& g))

-- Simpler
fmapT :: Functor h => (a -> b -> c) -> (a -> h b -> h c)
fmapT f = curry (fmap (uncurry f) . strength)
{-# INLINE fmapT #-}

#if 0
                     f              :: a -> b -> c
             uncurry f              :: a :* b -> c
       fmap (uncurry f)             :: h (a :* b) -> h c
                          strength  :: a :* h b -> h (a :* b)
       fmap (uncurry f) . strength  :: a :* h b -> h c
curry (fmap (uncurry f) . strength) :: a -> h b -> h c
#endif

-- Categorical version
fmapTC :: forall k h a b c.
          (ClosedCat k, FunctorCat k h, Strong k h, Ok3 k a b c)
       => (a `k` (b -> c)) -> (a `k` (h b -> h c))
fmapTC f = curry (fmapC (uncurry f) . strength)
           <+ okFunctor @k @h @(a :* b)
           <+ okProd    @k @a @(h b)
           <+ okProd    @k @a @b
           <+ okFunctor @k @h @b
           <+ okFunctor @k @h @c

-- Still simpler, restricting to fmapT id
fmapIdT :: Functor h => (b -> c) -> (h b -> h c)
fmapIdT = curry (fmapC apply . strength)
-- fmapIdT = fmapT id
{-# INLINE fmapIdT #-}

-- Categorical version
fmapIdTC :: forall k h b c . (ClosedCat k, Strong k h, FunctorCat k h, Ok2 k b c)
         => (b -> c) `k` (h b -> h c)
fmapIdTC = curry (fmapC apply . strength)
             <+ okFunctor @k @h @((b -> c) :* b)
             <+ okProd    @k @(h (b -> c)) @b
             <+ okFunctor @k @h @(b -> c)
             <+ okProd    @k @(b -> c) @(h b)
             <+ okFunctor @k @h @b
             <+ okFunctor @k @h @c
             <+ okProd    @k @(b -> c) @b
             <+ okExp     @k @b @c
-- fmapIdTC = fmapTC id
{-# INLINE fmapIdTC #-}

flipForkT :: forall k z a b. (IxProductCat k ((->) a), Ok2 k z b)
          => (z -> a -> b) -> (z `k` (a -> b))
-- flipForkT f = forkF (toCcc' P.. flip f)
-- flipForkT f = forkF (\ a -> toCcc' (flip f a))
flipForkT f = forkF (\ a -> toCcc' (\ z -> f z a))
{-# INLINE flipForkT #-}

--        f :: z -> a -> b
-- toCcc' f :: z `k` (a -> b)

-- flip f :: a -> z -> b  -- or forkF f
-- toCcc' . flip f :: a -> (z `k` b)
-- forkF (toCcc' . flip f) :: z `k` (a -> b)

forkUnforkT :: forall k h a b.
       (IxProductCat (->) h, Functor h, IxProductCat k h, Ok2 k a b)
    => (a -> h  b) -> (a `k` h b)
forkUnforkT f = forkF (fmap' toCcc' (unforkF f))
{-# INLINE forkUnforkT #-}

unforkF :: forall k h a b. (IxProductCat k h, Functor h, Ok2 k a b)
        => (a `k` h b) -> h (a `k` b)
unforkF g = fmap' (. g) exF <+ okIxProd @k @h @b
{-# INLINE unforkF #-}

--                           f  :: a -> h b
--                   unforkF f  :: h (a -> b)
--        toCcc' <$> unforkF f  :: h (a `k` b)
-- forkF (toCcc' <$> unforkF f) :: a `k` h b
