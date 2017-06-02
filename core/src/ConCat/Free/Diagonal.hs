{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | A convenient class for diagonizations

module ConCat.Free.Diagonal where

import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))
import Data.Pointed (Pointed(..))

import ConCat.Orphans ()

class (Functor f, Pointed f) => Diagonal f where
  -- diag zero one gives all zero except one on the diagonal.
  diag :: s -> s -> f (f s)

-- The Functor and Pointed superclass constraints are for convenience.
-- Remove if troublesome.

instance Diagonal U1   where
  diag _ _ = U1
  {-# INLINABLE diag #-}

instance Diagonal Par1 where
  diag _ o = Par1 (Par1 o)
  {-# INLINABLE diag #-}

instance Eq k => Diagonal ((->) k) where
  diag z o k k' = if k == k' then o else z

instance (Diagonal f, Diagonal g) => Diagonal (f :*: g) where
  diag z o = ((:*: point z) <$> diag z o) :*: ((point z :*:) <$> diag z o)
  {-# INLINABLE diag #-}

-- (:*: point zero) <$> diag zero one :: f ((f :*: g) s)
-- (point zero :*:) <$> diag zero one :: g ((f :*: g) s)

-- Note similarity of diag on f :*: g to (exl :*: exr)

instance (Diagonal g, Diagonal f, Traversable g, Applicative f)
      => Diagonal (g :.: f) where
  diag z o = Comp1 <$> Comp1 (sequenceA <$> diag (diag z o) (point (point z)))
  {-# INLINABLE diag #-}

-- Or use diag zero zero in place of point (point zero)

-- diag zero one :: f (f s)
-- point (point zero) :: f (f s)
-- diag (diag zero one) (point (point zero)) :: g (g (f (f s))
-- sequenceA <$> ... :: g (f (g (f s)))
-- Comp1 ... :: (g :.: f) (g (f s))
-- fmap Comp1 ... :: (g :.: f) ((g :.: f) s)
