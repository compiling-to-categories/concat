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
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation

module ConCat.AD where

import Prelude hiding (id,(.),curry,uncurry)
import qualified Prelude as P
import GHC.Exts (Coercible,coerce)

import GHC.Generics (Par1(..),(:.:)(..),(:*:)())
import Control.Newtype

import ConCat.Misc ((:*),inNew2,PseudoFun(..))
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat hiding (const)
import ConCat.Rep

newtype D s a b = D { unD :: a -> b :* L s a b }
-- data D s a b = D { unD :: a -> b :* L s a b }

-- TODO: generalize from L to any cartesian category

-- Differentiable linear function, given the function and linear map version
linearD :: (a -> b) -> L s a b -> D s a b
-- linearD f f' = D (f &&& const f')
linearD f f' = D (\ a -> (f a, f'))
{-# INLINE linearD #-}

-- TODO: have linearD accept *just* the L version and convert via lapply

-- instance Newtype (D s a b) where
--   type O (D s a b) = (a -> b :* L s a b)
--   pack f = D f
--   unpack (D f) = f

instance HasRep (D s a b) where
  type Rep (D s a b) = (a -> b :* L s a b)
  abst f = D f
  repr (D f) = f

instance Category (D s) where
  type Ok (D s) = OkLM s
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

instance ProductCat (D s) where
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
-- instance ClosedCat (D s)

--     • No instance for (OpCon (Exp (D s)) (Sat (OkLM s)))
--         arising from the superclasses of an instance declaration
--     • In the instance declaration for ‘ClosedCat (D s)’

{--------------------------------------------------------------------
    Other instances
--------------------------------------------------------------------}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

instance Num s => TerminalCat (D s) where
  it = linearD (const ()) zeroLM
  {-# INLINE it #-}

instance OkLM s b => ConstCat (D s) b where
  const b = D (const (b, zeroLM))
  {-# INLINE const #-}

--     • The constraint ‘HasL (V s b)’
--         is no smaller than the instance head
--       (Use UndecidableInstances to permit this)

instance OkLM s s => NumCat (D s) s where
  negateC = linearD negateC (scale (-1))
  addC    = linearD addC    jamLM
  mulC    = D (mulC &&& (\ (a,b) -> scale b `joinLM` scale a))
  powIC   = notDef "powC"
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

const' :: (a -> c) -> (a -> b -> c)
const' = (const .)

scalarD :: OkLM s s => (s -> s) -> (s -> s -> s) -> D s s s
scalarD f der = D (\ x -> let r = f x in (r, scale (der x r)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' g when only x
-- matters.

scalarR :: OkLM s s => (s -> s) -> (s -> s) -> D s s s
scalarR f f' = scalarD f (\ _ -> f')
-- scalarR f x = scalarD f (const x)
-- scalarR f = scalarD f . const
{-# INLINE scalarR #-}

scalarX :: OkLM s s => (s -> s) -> (s -> s) -> D s s s
scalarX f f' = scalarD f (\ x _ -> f' x)
-- scalarX f f' = scalarD f (\ x y -> const (f' x) y)
-- scalarX f f' = scalarD f (\ x -> const (f' x))
-- scalarX f f' = scalarD f (const . f')
-- scalarX f f' = scalarD f (const' f')
-- scalarX f = scalarD f . const'
{-# INLINE scalarX #-}

square :: Num a => a -> a
square a = a * a
{-# INLINE square #-}

instance (OkLM s s, Fractional s) => FractionalCat (D s) s where
  recipC = scalarR recip (negate . square)
  {-# INLINE recipC #-}

instance (OkLM s s, Floating s) => FloatingCat (D s) s where
  expC = scalarR exp id
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
  {-# INLINE expC #-}
  {-# INLINE sinC #-}
  {-# INLINE cosC #-}

instance (V s (Rep a) ~ V s a, Ok (L s) a, HasRep a) => RepCat (D s) a where
  reprC = linearD reprC' reprC'
  abstC = linearD abstC' abstC'

#if 0
instance (Coercible a b, V s a ~ V s b, Ok2 (L s) a b) => CoerceCat (D s) a b where
  coerceC = linearD coerceC coerceC
#else
instance ( CoerceCat (->) a b
         , CoerceCat (L s) a b
         -- , V s a ~ V s b
         -- , Coercible (V s a) (V s b)
         -- , Coercible (V s b (V s a s)) (V s a (V s a s))
         -- , Coercible (L s a a) (L s a b)
         -- , Ok2 (L s) a b
         ) => CoerceCat (D s) a b where
  coerceC = linearD coerceC coerceC
#endif

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

andDeriv :: forall s a b . (a -> b) -> (a -> b :* L s a b)
andDeriv _ = error "andDeriv called"
{-# NOINLINE andDeriv #-}
{-# RULES "andDeriv" forall h. andDeriv h = unD (reveal (ccc h)) #-}
{-# ANN andDeriv PseudoFun #-}

-- The reveal greatly improves simplification and speeds up compilation.

deriv :: forall s a b . (a -> b) -> (a -> L s a b)
deriv _ = error "deriv called"
{-# NOINLINE deriv #-}
-- {-# RULES "deriv" forall h. deriv h = snd . andDeriv h #-}
-- {-# RULES "deriv" forall h. deriv h = snd P.. andDeriv h #-}
{-# RULES "deriv" forall h. deriv h = ccc (snd . andDeriv h) #-}
{-# ANN deriv PseudoFun #-}

-- 2016-01-07: I thought the extra ccc would help with simplification, but I get
-- longer results rather than shorter in my limited testing.
