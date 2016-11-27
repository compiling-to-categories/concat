{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation using functions instead of linear maps

module ConCat.ADFun where

import Prelude hiding (id,(.),const,curry,uncurry)

import Control.Newtype

import ConCat.Misc ((:*),inNew2)
import ConCat.Category

newtype D a b = D { unD :: a -> b :* (a -> b) }

-- TODO: generalize from LM to any cartesian category

-- Differentiable linear function
linearD :: (a -> b) -> D a b
linearD f = D (f &&& const f)

instance Newtype (D a b) where
  type O (D a b) = (a -> b :* (a -> b))
  pack = D
  unpack = unD

instance Category D where
  id = linearD id
  D g . D f = D $ \ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f')

instance ProductCat D where
  exl = linearD exl
  exr = linearD exr
  D f &&& D g = D $ \ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g')

-- -- Don't define methods yet. I think I can optimize away the ClosedCat
-- -- operations in most cases. Once I'm happy with the results, define these
-- -- methods and turn off the optimizations.
-- instance ClosedCat D where
--   -- apply = D (\ (f,a) -> (f a, \ (df,da) -> undefined))

--     • No instance for (OpCon (Exp D) (Sat (OkLM s)))
--         arising from the superclasses of an instance declaration
--     • In the instance declaration for ‘ClosedCat D’
#if 0

applyD :: D (D a b :* a) b
applyD = D (\ (D h, a) ->
              let (b,b') = h a in
                (b,\ (df,da) -> df a + undefined)
           )

a :: a
D h :: D a b
h :: a -> b :* (a -> b)
(b,b') :: b :* (a -> b)
b :: b
b' :: a -> b

want :: D a b :* a -> b
#endif


{--------------------------------------------------------------------
    Other instances
--------------------------------------------------------------------}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

instance Num a => NumCat D a where
  negateC = linearD negateC
  addC    = linearD addC
  mulC    = D (mulC &&& (\ (a,b) (da,db) -> da*b + db*a))
  powIC   = notDef "powC"

const' :: (a -> c) -> (a -> b -> c)
const' = (const .)

scalarD :: Num s => (s -> s) -> (s -> s -> s) -> D s s
scalarD f der = D (\ x -> let r = f x in (r, (der x r *)))

-- Use scalarD with const f when only r matters and with const' g when only x
-- matters.

scalarR :: Num s => (s -> s) -> (s -> s) -> D s s
scalarR f = scalarD f . const

scalarX :: Num s => (s -> s) -> (s -> s) -> D s s
scalarX f = scalarD f . const'

square :: Num a => a -> a
square a = a * a

instance Fractional s => FractionalCat D s where
  recipC = scalarR recip (negate . square)

instance Floating s => FloatingCat D s where
  expC = scalarR exp id
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
