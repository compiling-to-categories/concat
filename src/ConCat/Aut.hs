{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automaton category

module ConCat.Aut where

import Prelude hiding (id,(.),curry,uncurry,const)

import Control.Newtype (Newtype(..))

import ConCat.Misc ((:*))
import qualified ConCat.Category as C
import ConCat.AltCat

newtype Aut k a b = Aut (a `k` (b :* Aut k a b))

instance Category (Aut k) where
  id = Aut (id &&& _)
