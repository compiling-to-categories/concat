-- SO test case, re: my HasFin instance for Bool.
--
-- David Banas <capn.freako@gmail.com>
-- February 9, 2018

{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Bogus.BoolHasFin where

import GHC.TypeLits
import Data.Finite.Internal (Finite(..))

class KnownNat (Card a) => HasFin a where
  type Card a :: Nat
  toFin :: a -> Finite (Card a)
  unFin :: Finite (Card a) -> a

instance HasFin Bool where
  type Card Bool = 2

  toFin False = Finite 0
  toFin True  = Finite 1

  unFin (Finite 0) = False
  unFin _          = True

