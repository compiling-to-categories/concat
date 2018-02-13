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
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

#include "ConCat/AbsTy.inc"
AbsTyPragmas

-- | A category of local approximations (and probably other uses)
module ConCat.Free.Affine where

import Prelude hiding (id,(.),curry,uncurry,const)
import Data.Key (Zip(..))

import ConCat.Misc ((:*))
import ConCat.Rep
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Free.VectorSpace hiding ((^+^))
import qualified ConCat.Free.VectorSpace as V
import ConCat.Free.LinearRow
import ConCat.AdditiveFun (Additive(..))

AbsTyImports

data Affine s a b = Affine (L s a b) b

linearA :: forall s a b. Ok2 (L s) a b => L s a b -> Affine s a b
linearA = flip Affine (unV @s zeroV)
{-# INLINE linearA #-}

applyA :: forall s a b. Ok2 (L s) a b => Affine s a b -> (a -> b)
applyA (Affine p u) a = add @s (lapply p a) u
{-# INLINE applyA #-}

instance HasRep (Affine s a b) where
  type Rep (Affine s a b) = L s a b :* b
  abst (m,b) = Affine m b
  repr (Affine m b) = (m,b)

AbsTy(Affine s a b)

instance Ok2 (L s) a b => Additive (Affine s a b) where
  zero = linearA zeroLM
  Affine p u ^+^ Affine q v = Affine (p `addLM` q) (add @s u v)
  {-# INLINE zero #-}
  {-# INLINE (^+^) #-}

instance Category (Affine s) where
  type Ok (Affine s) = Ok (L s)
  id = linearA id
  (.) = inAbst2 $ \ (q,v) (p,u) -> (q . p, add @s (lapply q u) v)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

-- Semantic homomorphism: applyA g . applyA f == applyA (g . f)

-- applyA (Affine q v) . applyA (Affine p u) == applyA (Affine q v . Affine p u)

--   applyA (Affine q v) . applyA (Affine p u)
-- == \ a -> q (p a + u) + v
-- == \ a -> (q (p a) + q u) + v
-- == \ a -> (q . p) a + (q u + v)
-- == applyA (Affine (q . p) (q u + v))

instance MonoidalPCat (Affine s) where
  (***) = inAbst2 $ \ (p,u) (q,v) -> (p *** q, (u,v))
  {-# INLINE (***) #-}

--    applyA (Affine p u) *** applyA (Affine q v)
-- == \ (a,b) -> (applyA (Affine p u) *** applyA (Affine q v)) a
-- == \ (a,b) -> (applyA (Affine p u) a, applyA (Affine q v) b)
-- == \ (a,b) -> (p a + u, q b + v)
-- == \ (a,b) -> (p a,q b) + (u,v)
-- == \ (a,b) -> (p *** q) (a,b) + (u,v)
-- == applyA (Affine (p *** q) (u,v))

instance ProductCat (Affine s) where
  exl = linearA exl
  exr = linearA exr
  dup = linearA dup
  -- (&&&) = inAbst2 $ \ (p,u) (q,v) -> (p &&& q, (u,v))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  -- {-# INLINE (&&&) #-}

{--------------------------------------------------------------------
    Move elsewhere
--------------------------------------------------------------------}

add :: forall s a. (HasV s a, Zip (V s a), Num s) => a -> a -> a
add = onV2 @s (V.^+^)
{-# INLINE add #-}
