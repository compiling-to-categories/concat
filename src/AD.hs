{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wall #-}

-- | Generalized automatic differentiation

module AD where

import Prelude hiding (id,(.))

import Misc
import ConCat

newtype D k a b = D (a -> b :* (a `k` b))

linearD :: (a -> b) -> (a `k` b) -> D k a b
linearD f f' = D (f &&& const f')

linearD' :: (forall cat. Category cat => a `cat` b) -> Category k => D k a b
linearD' f = D (f &&& const f)

(@@) :: (Category k, Ok k a, Ok k b, Ok k c) =>
        D k b c -> D k a b -> D k a c
D q @@ D p = D $ \ a ->
  let (b,p') = p a
      (c,q') = q b
  in
    (c, q' . p')

instance Category k => Category (D k) where
  type Ok (D k) = Ok k
  id  = linearD id id
  (.) = (@@)
