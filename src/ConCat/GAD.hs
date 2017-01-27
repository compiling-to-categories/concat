{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Generalized automatic differentiation

module ConCat.GAD where

import Prelude hiding (id,(.),curry,uncurry,const)
import qualified Prelude as P
import GHC.Exts (Coercible,coerce)

import GHC.Generics (Par1(..),(:.:)(..),(:*:)())
import Control.Newtype

import ConCat.Misc ((:*),inNew2,PseudoFun(..))
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Rep

newtype GD k a b = D { unD :: a -> b :* (a `k` b) }
-- data GD k a b = D { unD :: a -> b :* (a `k` b) }

-- Differentiable linear function, given the function and linear map version
linearD :: (a -> b) -> (a `k` b) -> GD k a b
-- linearD f f' = D (f &&& const f')
linearD f f' = D (\ a -> (f a, f'))
{-# INLINE linearD #-}

-- TODO: have linearD accept *just* the L version and convert via lapply

-- instance Newtype (D s a b) where
--   type O (D s a b) = (a -> b :* L s a b)
--   pack f = D f
--   unpack (D f) = f

instance HasRep (GD k a b) where
  type Rep (GD k a b) = (a -> b :* (a `k` b))
  abst f = D f
  repr (D f) = f

instance Category k => Category (GD k) where
  type Ok (GD k) = Ok k
  id = linearD id id
  D g . D f = D (\ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f'))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

--   (.) = inNew2 $ \ g f -> \ a ->
--     let (b,f') = f a
--         (c,g') = g b
--     in
--       (c, g' . f')

--   (.) = inNew2 $ \ g f -> second (uncurry (.)) . rassocP . first g . f

--   D g . D f = D $ \ a ->
--     let (b,f') = f a
--         (c,g') = g b
--     in
--       (c, g' . f')

instance ProductCat k => ProductCat (GD k) where
  exl = linearD exl exl
  exr = linearD exr exr
  D f &&& D g = D (\ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g'))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

--   (&&&) = inNew2 $ \ f g -> \ a ->
--     let (b,f') = f a
--         (c,g') = g a
--     in
--       ((b,c), f' &&& g')

--   (&&&) = inNew2 $ \ f g -> second (uncurry (&&&)) . transposeP . (f &&& g)

--   D f &&& D g = D $ \ a ->
--     let (b,f') = f a
--         (c,g') = g a
--     in
--       ((b,c), f' &&& g')

-- -- Don't define methods yet. I think I can optimize away the ClosedCat
-- -- operations in most cases. Once I'm happy with the results, define these methods and turn off the optimizations.
-- instance ClosedCat (GD k)

--     • No instance for (OpCon (Exp (GD k)) (Sat (Ok k)))
--         arising from the superclasses of an instance declaration
--     • In the instance declaration for ‘ClosedCat (GD k)’

{--------------------------------------------------------------------
    Other instances
--------------------------------------------------------------------}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

instance (RepCat (->) a r, RepCat k a r) => RepCat (GD k) a r where
  reprC = linearD reprC reprC
  abstC = linearD abstC abstC

#if 0
instance (Coercible a b, V s a ~ V s b, Ok2 k a b) => CoerceCat (GD k) a b where
  coerceC = linearD coerceC coerceC
#else
instance ( CoerceCat (->) a b
         , CoerceCat k a b
         ) => CoerceCat (GD k) a b where
  coerceC = linearD coerceC coerceC
#endif

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

andDeriv :: forall k a b . (a -> b) -> (a -> b :* (a `k` b))
andDeriv _ = error "andDeriv called"
{-# NOINLINE andDeriv #-}
-- {-# RULES "andDeriv" forall h. andDeriv h = unD (reveal (ccc h)) #-}
-- {-# RULES "andDeriv" forall h. andDeriv h = unD (ccc h) #-}
{-# RULES "andDeriv" forall h. andDeriv h = unD (ccc (ccc h)) #-}
{-# ANN andDeriv PseudoFun #-}

-- The extra ccc allows us to use ClosedCat (->) and then apply rewrite rules to
-- eliminate the closed operations.

-- The reveal greatly improved simplification and sped up compilation.
-- Try removing, and retest.

deriv :: forall k a b . (a -> b) -> (a -> (a `k` b))
deriv _ = error "deriv called"
{-# NOINLINE deriv #-}
-- {-# RULES "deriv" forall h. deriv h = snd . andDeriv h #-}
-- {-# RULES "deriv" forall h. deriv h = snd P.. andDeriv h #-}
{-# RULES "deriv" forall h. deriv h = ccc (snd . andDeriv h) #-}
{-# ANN deriv PseudoFun #-}

-- 2016-01-07: The extra ccc helped with simplification.
-- Occassionally try without, and compare results.
