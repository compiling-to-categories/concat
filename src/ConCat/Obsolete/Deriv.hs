{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

module ConCat.Deriv where

import Prelude hiding (id,(.),curry,uncurry)
import GHC.Generics ((:*:)(..))

import Data.Constraint hiding ((&&&))
import Control.Newtype
import Data.MemoTrie

import ConCat.Misc
import ConCat.Category
import ConCat.Additive
import ConCat.Semimodule
import ConCat.FLMap

data D s a b = D (a -> b) (a -> LMap s a b)

instance Newtype (D s a b) where
  type O (D s a b) = (a -> b) :* (a -> LMap s a b)
  pack (f,f') = D f f'
  unpack (D f f') = (f,f')

instance OkL2 s a b => Additive (D s a b) where
  zero = pack zero
  (^+^) = inNew2 (^+^)

instance OkL2 s a b => Semimodule (D s a b) where
  type Scalar (D s a b) = Scalar (O (D s a b))
  (*^) s = inNew ((*^) s)

instance Category (D s) where
  type Ok (D s) = OkL s
  id = D id (const id)
  D g g' . D f f' = D (g . f) (\ a -> g' (f a) . f' a)

instance ProductCat (D s) where
  type Prod (D s) = (:*)
  exl = D exl (const exl)
  exr = D exr (const exr)
  D f f' &&& D g g' = D (f &&& g) (\ a -> f' a &&& g' a)

instance OpCon (D s) (OkL s) where inOp = Sub Dict

-- instance ClosedCat (D s) where
--   type Exp (D s) = D s
--   apply :: forall s a b. OkL2 s a b => D s (D s a b :* a) b
--   apply = D (\ (D h _, a) -> h a)
--             (\ (D _ h',a) -> (applyTo a ||| h' a) . first (exl . unpackL))
--   curry (D f f') = D (curry f) undefined -- (\ a -> flipFL (\ b -> f' (a,b) . inl))

#if 0

curry :: D s (a :* b) c -> D s a (D s b c)

f  :: a :* b -> c
f' :: a :* b -> D s (a :* b) c

#endif


-- Types for apply:
#if 0
             unpackL  :: LMap s (D s a b) ((a -> b) :* (a -> LMap s a b))
       exl . unpackL  :: LMap s (D s a b) (a -> b)
first (exl . unpackL) :: LMap s (D s a b :* a) ((a -> b) :* a)

applyTo a          :: LMap s (a -> b) b
              h' a :: LMap s a b
applyTo a ||| h' a :: LMap s ((a -> b) :* a) b

(applyTo a ||| h' a) . first (exl unpackL) :: LMap s (D s a b :* a) b

(\ (D _ h',a) -> (applyTo a ||| h' a) . first (exl unpackL))
  :: (D s a b :* a) -> LMap s (D s a b :* a) b
#endif
