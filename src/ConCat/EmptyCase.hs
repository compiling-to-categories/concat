{-# LANGUAGE CPP, TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -ddump-simpl -Wno-unused-imports #-}

-- | Tracking down an issue with GHC generating an empty case expression

module ConCat.EmptyCase where

import GHC.Exts (lazy)

#if 1

import ConCat.Misc ((:*))
import ConCat.Free.LinearRow
import ConCat.AD
import ConCat.AltCat (ccc)

type R = Float

bar :: R -> R :* L R R R
bar = lazy unD (ccc id)

#elif 1

type (:*) = (,)

data L s a b = L b

data D s a b = D { unD :: a -> b :* L s a b }

-- | Pseudo function to trigger rewriting to CCC form.
ccc :: (a -> b) -> (a `k` b)
ccc f = ccc f
{-# NOINLINE ccc #-}
-- {-# RULES "ccc error" [0] forall f. ccc f = error "ccc: not implemented" #-}

type R = Float

bar :: R -> R :* L R R R
bar = lazy unD (ccc id)

#else

data D a b = D { unD :: a -> b }

foo :: (a -> b) -> (a `k` b)
foo f = foo f
{-# NOINLINE foo #-}

bar :: Int -> Int
bar = lazy unD (foo id)

#endif
