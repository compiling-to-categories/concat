{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | GUI category

module ConCat.Gui where

import Prelude hiding (id,(.),curry,uncurry,const)
import GHC.Exts (Coercible,coerce)

import Control.Newtype

import ConCat.Misc ((:*),(:+),inNew,inNew2)
import ConCat.Category
import ConCat.AltCat (ccc)

data In   :: * -> * where
  NoI     :: In a
  SliderI :: String -> Int -> Int -> Int -> In Int
  PairI   :: In a -> In b -> In (a :* b)

deriving instance Show (In a)

infixr 9 :-->

data Out  :: * -> * where
  NoO     :: Out a
  SliderO :: String -> Int -> Int -> Int -> Out Int
  PairO   :: Out a -> Out b -> Out (a :* b)
  (:-->)  :: In a -> Out b -> Out (a -> b)

deriving instance Show (Out a)

data Gui a b = Gui (In a) (Out b) deriving Show

instance Newtype (Gui a b) where
  type O (Gui a b) = In a :* Out b
  pack (a,b) = Gui a b
  unpack (Gui a b) = (a,b)
  unpack g = error ("unpack Gui: " ++ show g)

noGui :: Gui a b
noGui = pack (NoI,NoO)

instance Category Gui where
  id = noGui
  (.) = inNew2 (\ (_,c) (a,_) -> (a,c))

instance ProductCat Gui where
  exl = noGui
  exr = noGui
  (&&&) = inNew2 (\ (a,c) (a',d) -> (a, c `PairO` d))
