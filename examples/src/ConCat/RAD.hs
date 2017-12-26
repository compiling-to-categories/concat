{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Reverse mode AD

module ConCat.RAD where

import Prelude hiding (id,(.),const)

import ConCat.Misc ((:*),Yes1)
import ConCat.Category
import ConCat.Additive
import ConCat.DualAdditive
import ConCat.GAD

-- Differentiable functions
type RAD = GD Dual

type instance GDOk Dual = Yes1

mkD :: (a -> b :* (b -> a)) -> RAD a b
mkD h = D (second Dual . h)

-- mkD f f' = D (\ a -> (f a, Dual (f' a)))

-- Affine functions with function and transposed derivative
affine :: (a -> b) -> (b -> a) -> RAD a b
affine f f' = mkD (f &&& const f')

instance Additive b => ConstCat RAD b where
  const b = affine (const b) (const zero)
            -- mkD (const (b, zero))
  {-# INLINE const #-}

-- TODO: Tweak GD, ADFun, and AD to use "affine", and apply it to const.

instance TerminalCat RAD where
  it = const ()
  {-# INLINE it #-}

instance (Num s, Additive s) => NumCat RAD s where
  addC    = affine addC dup
  negateC = affine negateC negateC
  mulC    = D (\ (u,v) -> (u*v, Dual (\ s -> (s*v,s*u))))
  powIC   = notDef "powIC"       -- TODO
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

-- Variable ‘s’ occurs more often
--   in the constraint ‘Additive s’ than in the instance head
-- (Use UndecidableInstances to permit this)

-- Orphan instance:
--   instance forall s. (Num s, Additive s) => NumCat RAD s

-- I think I could remove the 'Additive s' superclass constraint from
-- 'NumCat RAD s' if I remove the 'Ok s' superclass constraint from the
-- NumCat class definition.

scalarD :: Num s => (s -> s) -> (s -> s -> s) -> RAD s s
scalarD f d = D (\ x -> let r = f x in (r, Dual (* d x r)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' . g when only x
-- matters.

scalarR :: Num s => (s -> s) -> (s -> s) -> RAD s s
scalarR f x = scalarD f (const x)
{-# INLINE scalarR #-}

scalarX :: Num s => (s -> s) -> (s -> s) -> RAD s s
scalarX f f' = scalarD f (const . f')
{-# INLINE scalarX #-}

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

andGradR :: Num s => (a -> s) -> (a -> s :* a)
andGradR = (fmap.fmap.second) (($ 1) . unDual) andDeriv
{-# INLINE andGradR #-}

gradR :: Num s => (a -> s) -> (a -> a)
gradR = (fmap.fmap) snd andGradR
{-# INLINE gradR #-}
