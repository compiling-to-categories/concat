{-# LANGUAGE CPP #-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies            #-}

-- #define Alias

#ifdef Alias
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
#endif

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Experimenting with an example. The plugin doesn't find the needed instances
-- when they're declared in the same module as the example. Hm.

module ConCat.LC where

import Data.Constraint (Dict(..),(:-)(..))

import ConCat.Misc ((:*),R)
#ifdef Alias
import ConCat.Misc (type (&+&))
#endif
import Data.Key (Zip)

import ConCat.Free.VectorSpace (HasV(..))
import ConCat.AltCat (OpCon(..),Sat(..),type (|-)(..))

import ConCat.Free.LinearRow
import ConCat.ADFun (RepresentableVE)
import ConCat.Additive (Additive)
import ConCat.Circuit



#ifdef Alias

type OkLC = OkLM R &+& GenBuses

#else

class    (OkLM R a, GenBuses a) => OkLC a
instance (OkLM R a, GenBuses a) => OkLC a

--     • The constraint ‘OkLM R a’ is no smaller than the instance head
--       (Use UndecidableInstances to permit this)
--     • In the instance declaration for ‘OkLC a’
-- test/Examples.hs:688:10-41: error: …
--     • The constraint ‘GenBuses a’ is no smaller than the instance head
--       (Use UndecidableInstances to permit this)

instance OpCon (:*) (Sat OkLC) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

-- type HasLin s a b = (HasV s a, HasV s b, HasL (V s a), Zip (V s b), Num s)

class    (HasV R a, HasL (V R a), Zip (V R a), Additive a, GenBuses a) => OkLFC a
instance (HasV R a, HasL (V R a), Zip (V R a), Additive a, GenBuses a) => OkLFC a

instance OpCon (:*) (Sat OkLFC) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}


class    (RepresentableVE R a, GenBuses a) => OkLFC' a
instance (RepresentableVE R a, GenBuses a) => OkLFC' a

instance OpCon (:*) (Sat OkLFC') where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

#endif
