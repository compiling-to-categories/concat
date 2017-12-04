{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | A category of local approximations (and probably other uses)

module ConCat.Local where

import Prelude hiding (id,(.),curry,uncurry,const)
import Control.Applicative (pure,liftA2)

import Control.Newtype
import Data.Copointed
import Data.Constraint (Dict(..),(:-)(..))

import ConCat.Misc ((:*),inNew2,type (&&))
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Free.LinearRow
-- import ConCat.Rep

newtype Local k a b = Local (a -> (a `k` b))

instance Newtype (Local k a b) where
  type O (Local k a b) = a -> (a `k` b)
  pack f = Local f
  unpack (Local f) = f

simpleL :: (a `k` b) -> Local k a b
simpleL f = Local (pure f)

class    (Ok k a, Copointed (k a)) => OkLocal k a 
instance (Ok k a, Copointed (k a)) => OkLocal k a 

-- • Illegal constraint ‘Ok k a’ in a superclass context
--     (Use UndecidableInstances to permit this)
-- • Potential superclass cycle for ‘OkLocal’
--     one of whose superclass constraints is headed by a type family:
--       ‘Ok k a’
--   Use UndecidableSuperClasses to accept this

instance Category k => Category (Local k) where
  type Ok (Local k) = OkLocal k
  id = simpleL id
  (.) = inNew2 $ \ g f -> \ a -> let f' = f a
                                     g' = g (copoint f')
                                 in
                                   g' . f'

#if 0

type OkCart k = OpCon (Prod k) (Sat (Ok (Local k)))

instance OpCon (:*) (Sat (Ok k)) => OpCon (:*) (Sat (OkLocal k)) where
  inOp :: (Sat (OkLocal k) a, Sat (OkLocal k) b) |- Sat (OkLocal k) (a :* b)
  inOp = Entail (Sub Dict) -- <+ okProd @k @a @b

-- Could not deduce (Copointed (k (a, b)))

-- instance OpCon (:*) (Sat (Ok k)) => OpCon (:*) (Sat (OkLocal k)) where
--   inOp = Entail (Sub Dict)
--   {-# INLINE inOp #-}

instance (OkCart k, ProductCat k)
      => ProductCat (Local k) where
  exl = simpleL exl
  exr = simpleL exr
  (&&&) = (inNew2.liftA2) (&&&)

--    Local f &&& Local g
-- == Local (\ a -> f a &&& g a)
-- == Local (\ a da -> (f a da, g a da)
  
-- Affine approximation. Later make explicit via ConCat.Free.Affine.
instance (Num a, Copointed ((->) a)) => NumCat (Local (->)) a where
  negateC = Local (\ x dx -> - (x + dx))
  addC = Local (\ (x,y) (dx,dy) -> x + y + dx + dy)
  mulC = Local (\ (x,y) (dx,dy) -> x*y + dy*x + dx*y)

#endif
