{-# LANGUAGE ConstraintKinds #-}
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
import qualified Prelude as P
import GHC.Exts (Coercible,coerce) -- inline

import Data.Pointed (Pointed(..))
import Data.Key (Zip(..))

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

-- TODO: Maybe use the following function-only definition instead, and wrap
-- toCcc' around it in the plugin.

type Strong h = (Zip h, Pointed h)

-- Functorial strength
strength :: (Zip h, Pointed h) => a :* h b -> h (a :* b)
strength = zipC . first pointC
{-# INLINE strength #-}

fmapT1 :: forall h a b c. Strong h => (a -> b -> c) -> (a -> h b -> h c)
fmapT1 f = P.curry (fmapC (P.uncurry f) . strength)
{-# INLINE fmapT1 #-}

fmapT2 :: forall h a b c. (Zip h, Pointed h)
       => (a -> b -> c) -> (a -> h b) -> (a -> h c)
-- fmapT2 f g = fmapC (P.uncurry f) . strength . (id &&& g)
fmapT2 f g = fmapC (P.uncurry f) . zipC . (point &&& g)
{-# INLINE fmapT2 #-}

#if 0

id &&& g          :: a -> a :* h b
strength          :: a :* h b -> h (a :* b)
fmapC (uncurry f) :: h (a :* b) -> h c

pointC &&& g      :: a -> h a * h b
zipC              :: h a :* h b -> h (a :* b)
fmapC (uncurry f) :: h (a :* b) -> h c

#endif

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

-- castConstT :: forall a b b'. Coercible b b' => b -> (a -> b')
-- -- castConstT b = P.const (coerce b)
-- castConstT b = const (coerce b)
-- {-# INLINE castConstT #-}

castConstT :: forall k a b b'. (ConstCat k b', Ok k a, Coercible b b')
           => b -> (a `k` b')
castConstT b = const (coerce b)
{-# INLINE castConstT #-}

bottomT :: forall k a b. (Category k, TerminalCat k, BottomCat k () b, Ok2 k a b)
        => a `k` b
bottomT = bottomC . it
{-# INLINE bottomT #-}
