{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation

module ConCat.AD where

import Prelude hiding (id,(.),curry,uncurry)

import Control.Newtype

import ConCat.Misc ((:*),inNew2,PseudoFun(..))
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat hiding (const)

data D s a b = D (a -> b :* L s a b)

-- TODO: "data" --> "newtype" when the plugin is up for it.

unD :: D s a b -> (a -> b :* L s a b)
unD (D f) = f
{-# INLINE unD #-}

-- TODO: generalize from L to any cartesian category

-- Differentiable linear function, given the function and linear map version
linearD :: (a -> b) -> L s a b -> D s a b
linearD f f' = D (f &&& const f')
{-# INLINE linearD #-}

-- TODO: have linearD accept *just* the L version and convert via lapply

instance Newtype (D s a b) where
  type O (D s a b) = (a -> b :* L s a b)
  pack f = D f
  unpack (D f) = f

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

instance (Num s, HasV s b, HasL (V s b)) => ConstCat (D s) b where
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
scalarR f = scalarD f . const
{-# INLINE scalarR #-}

scalarX :: OkLM s s => (s -> s) -> (s -> s) -> D s s s
scalarX f = scalarD f . const'
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

{--------------------------------------------------------------------
    Utilities
--------------------------------------------------------------------}

dfun :: forall s a b . (a -> b) -> (a -> b :* L s a b)
dfun _ = error "dfun called"
{-# NOINLINE dfun #-}
{-# RULES "dfun" forall h. dfun h = unD' (reveal (ccc h)) #-}
{-# ANN dfun PseudoFun #-}

unD' :: D s a b -> a -> b :* L s a b
#if 0
unD' d = unD d
{-# INLINE [0] unD' #-}
#else
unD' _ = error "unD' called"
{-# NOINLINE unD' #-}
{-# RULES "unD'" [0] unD' = unD #-}
#endif

-- Experiment: inline on demand
{-# RULES "ccc of unD'" forall q. ccc (unD' q) = ccc (unD q) #-}
{-# RULES "unD' of D" forall f. unD' (D f) = f #-}

