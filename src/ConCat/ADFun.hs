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
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat

-- newtype D a b = D { unD :: a -> b :* (a -> b) }
-- newtype D a b = D (a -> b :* (a -> b))
data D a b = D (a -> b :* (a -> b))
-- data D a b = D { unD :: a -> b :* (a -> b) }

-- TODO: revert to newtype, and fix Plugin to handle it correctly.

unD :: D a b -> (a -> b :* (a -> b))
unD (D f) = f
{-# INLINE unD #-}

-- TODO: generalize from LM to any cartesian category

-- Differentiable linear function
linearD :: (a -> b) -> D a b
linearD f = D (f &&& const f)
{-# INLINE linearD #-}

instance Newtype (D a b) where
  type O (D a b) = a -> b :* (a -> b)
  pack = D
  unpack = unD

instance Category D where
  id = linearD id
  D g . D f = D $ \ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f')
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance ProductCat D where
  exl = linearD exl
  exr = linearD exr
  D f &&& D g = D $ \ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g')
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

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

instance TerminalCat D where
  it = linearD (const ())
  {-# INLINE it #-}

instance Num b => ConstCat D b where
  const b = D (const (b, const 0))
  {-# INLINE const #-}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

instance Num a => NumCat D a where
  negateC = linearD negateC
  addC    = linearD addC
  mulC    = D (mulC &&& (\ (a,b) (da,db) -> da*b + db*a))
  powIC   = notDef "powC"
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

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

