{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}

-- | Category of Isomorphisms.

module ConCat.Isomorphism where

import Prelude hiding (id, (.), const)  -- Coming from ConCat.AltCat.
import ConCat.AltCat
import qualified ConCat.Category

data Iso k a b = Iso (a `k` b) (b `k` a)

instance Category k => Category (Iso k) where
  id = Iso id id
  Iso g g' . Iso f f' = Iso (g . f) (f' . g')

