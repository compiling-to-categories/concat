{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | A category of local approximations (and probably other uses)

module ConCat.Affine where

import Prelude hiding (id,(.),curry,uncurry,const)
import Control.Applicative (pure,liftA2)

import Control.Newtype
import Data.Key (Zip(..))
import Data.Copointed

import ConCat.Misc ((:*),inNew2)
import qualified ConCat.Category as C
import ConCat.AltCat
-- import ConCat.Rep
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow

data Affine s a b = Affine (L s a b) b

linearA :: forall s a b. Ok2 (L s) a b => L s a b -> Affine s a b
linearA = flip Affine (unV @s zeroV)

applyA :: forall s a b. Ok2 (L s) a b => Affine s a b -> (a -> b)
applyA (Affine p u) a = add @s (lapply p a) u

instance Newtype (Affine s a b) where
  type O (Affine s a b) = L s a b :* b
  pack (m,b) = Affine m b
  unpack (Affine m b) = (m,b)

instance Category (Affine s) where
  type Ok (Affine s) = Ok (L s)
  id = linearA id
  (.) = inNew2 $ \ (q,v) (p,u) -> (q . p, add @s (lapply q u) v)

-- Semantic homomorphism: applyA g . applyA f == applyA (g . f)

-- applyA (Affine q v) . applyA (Affine p u) == applyA (Affine q v . Affine p u)

--   applyA (Affine q v) . applyA (Affine p u)
-- == \ a -> q (p a + u) + v
-- == \ a -> (q (p a) + q u) + v
-- == \ a -> (q . p) a + (q u + v)
-- == applyA (Affine (q . p) (q u + v))

instance ProductCat (Affine s) where
  exl = linearA exl
  exr = linearA exr
  (&&&) = inNew2 $ \ (p,u) (q,v) -> (p &&& q, (u,v))

--    applyA (Affine p u) &&& applyA (Affine q v)
-- == \ a -> (applyA (Affine p u) &&& applyA (Affine q v)) a
-- == \ a -> (applyA (Affine p u) a, applyA (Affine q v) a)
-- == \ a -> (p a + u, q a + v)
-- == \ a -> (p a,q a) + (u,v)
-- == \ a -> (p &&& q) a + (u,v)
-- == applyA (Affine (p &&& q) (u,v))

{--------------------------------------------------------------------
    Move elsewhere
--------------------------------------------------------------------}

add :: forall s a. (HasV s a, Zip (V s a), Num s) => a -> a -> a
add = onV2 @s (^+^)
