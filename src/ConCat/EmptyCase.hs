{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -ddump-simpl #-}

-- | Tracking down an issue with GHC generating an empty case expression

module ConCat.EmptyCase where

infixl 7 :*
type (:*)  = (,)

data L s a b = L b

data D s a b = D { unD :: a -> b :* L s a b }

-- | Pseudo function to trigger rewriting to CCC form.
ccc :: (a -> b) -> (a `k` b)
ccc f = ccc f
{-# NOINLINE ccc #-}
-- {-# RULES "ccc error" [0] forall f. ccc f = error "ccc: not implemented" #-}

type R = Float

bar :: R -> R :* L R R R
bar = unD (ccc id)
