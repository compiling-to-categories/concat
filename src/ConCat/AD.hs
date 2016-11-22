{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation

module ConCat.AD where

import Prelude hiding (id,(.),const,curry,uncurry)

import Control.Newtype

import ConCat.Misc ((:*),inNew2)
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow
import ConCat.Category

newtype D s a b = D (a -> b :* LM s a b)

-- TODO: generalize from LM to any cartesian category

-- Differentiable linear function, given the function and linear map version
linearD :: (a -> b) -> LM s a b -> D s a b
linearD f f' = D (f &&& const f')

instance Newtype (D s a b) where
  type O (D s a b) = (a -> b :* LM s a b)
  pack f = D f
  unpack (D f) = f

instance Category (D s) where
  type Ok (D s) = OkLM s
  id = linearD id id

  (.) = inNew2 $ \ g f -> \ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f')

--   (.) = inNew2 $ \ g f -> second (uncurry (.)) . rassocP . first g . f

--   D g . D f = D $ \ a ->
--     let (b,f') = f a
--         (c,g') = g b
--     in
--       (c, g' . f')


instance ProductCat (D s) where
  exl = linearD exl exl
  exr = linearD exr exr

  (&&&) = inNew2 $ \ f g -> \ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g')

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

instance OkLM s s => NumCat (D s) s where
  negateC = linearD negateC (scale (-1))
  addC    = linearD addC    jamLM
  mulC    = D (mulC &&& (\ (a,b) -> scale b `joinLM` scale a))
  powIC   = notDef "powC"

const' :: (a -> c) -> (a -> b -> c)
const' = (const .)

scalarD :: OkLM s s => (s -> s) -> (s -> s -> s) -> D s s s
scalarD f der = D (\ x -> let r = f x in (r, scale (der x r)))

-- Use scalarD with const f when only r matters and with const' g when only x
-- matters.

scalarR :: OkLM s s => (s -> s) -> (s -> s) -> D s s s
scalarR f = scalarD f . const

scalarX :: OkLM s s => (s -> s) -> (s -> s) -> D s s s
scalarX f = scalarD f . const'

square :: Num a => a -> a
square a = a * a

instance (OkLM s s, Fractional s) => FractionalCat (D s) s where
  recipC = scalarR recip (negate . square)

instance (OkLM s s, Floating s) => FloatingCat (D s) s where
  expC = scalarR exp id
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
