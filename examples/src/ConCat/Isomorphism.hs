{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}

-- | Category of Isomorphisms.

module ConCat.Isomorphism where

import Prelude hiding (id, (.), const)  -- Coming from ConCat.AltCat.
import ConCat.AltCat
import qualified ConCat.Category

infix 0 :<->
data Iso k a b = (a `k` b) :<-> (b `k` a)

inverse :: Iso k a b -> Iso k b a
inverse (f :<-> f') = f' :<-> f

instance Category k => Category (Iso k) where
  type Ok (Iso k) = Ok k
  id = id :<-> id
  (g :<-> g') . (f :<-> f') = (g . f) :<-> (f' . g')

instance MonoidalPCat k => MonoidalPCat (Iso k) where
  (f :<-> f') *** (g :<-> g') = (f *** g) :<-> (f' *** g')

instance MonoidalSCat k => MonoidalSCat (Iso k) where
  (f :<-> f') +++ (g :<-> g') = (f +++ g) :<-> (f' +++ g')

isoFwd :: Iso k a b -> (a `k` b)
isoFwd (f :<-> _) = f

isoRev :: Iso k a b -> (b `k` a)
isoRev (_ :<-> f') = f'

infix 0 <->
type (<->) = Iso (->)

-- Old notation
pattern Iso :: (a `k` b) -> (b `k` a) -> Iso k a b
pattern Iso f f' = f :<-> f'
