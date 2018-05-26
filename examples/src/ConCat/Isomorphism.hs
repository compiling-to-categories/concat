{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}

-- | Category of Isomorphisms.

module ConCat.Isomorphism where

import Prelude hiding (id, (.), const)  -- Coming from ConCat.AltCat.
import ConCat.AltCat
import qualified ConCat.Category

data Iso k a b = Iso (a `k` b) (b `k` a)

inverse :: Iso k a b -> Iso k b a
inverse (Iso f f') = Iso f' f

instance Category k => Category (Iso k) where
  type Ok (Iso k) = Ok k
  id = Iso id id
  Iso g g' . Iso f f' = Iso (g . f) (f' . g')

instance MonoidalPCat k => MonoidalPCat (Iso k) where
  Iso f f' *** Iso g g' = Iso (f *** g) (f' *** g')

instance MonoidalSCat k => MonoidalSCat (Iso k) where
  Iso f f' +++ Iso g g' = Iso (f +++ g) (f' +++ g')

isoFwd :: Iso k a b -> (a `k` b)
isoFwd (Iso g _) = g

isoRev :: Iso k a b -> (b `k` a)
isoRev (Iso _ h) = h

infix 0 <->
type (<->) = Iso (->)
