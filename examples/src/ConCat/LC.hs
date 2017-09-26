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


-- | 

module ConCat.LC where

import Data.Constraint (Dict(..),(:-)(..))

import ConCat.Misc ((:*),R)
#ifdef Alias
import ConCat.Misc (type (&+&))
#endif
import ConCat.AltCat (OpCon(..),Sat(..),type (|-)(..))

import ConCat.Free.LinearRow
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

#endif
