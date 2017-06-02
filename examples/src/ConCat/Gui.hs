{-# LANGUAGE TupleSections #-}
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

instance Monoid (Out a) where
  mempty = NoO
  NoO `mappend` b = b
  a `mappend` _ = a

infixr 9 :-->

data Out  :: * -> * where
  NoO     :: Out a
  SliderO :: String -> Int -> Int -> Int -> Out Int
  PairO   :: Out a -> Out b -> Out (a :* b)
  (:-->)  :: In a -> Out b -> Out (a -> b)

-- unFunO :: Out (a -> b) -> In a :* Out b
-- unFunO (a :--> b) = (a,b)
-- unFunO o = error ("unFunO: " ++ show o)

deriving instance Show (Out a)

instance Monoid (In a) where
  mempty = NoI
  NoI `mappend` b = b
  a `mappend` _ = a

data Gui a b = Gui (In a) (Out b) deriving Show

instance Newtype (Gui a b) where
  type O (Gui a b) = In a :* Out b
  pack (a,b) = Gui a b
  unpack (Gui a b) = (a,b)

input :: In a -> Gui a a
input = pack . (,NoO)

output :: Out a -> Gui a a
output = pack . (NoI,)

noGui :: Gui a b
noGui = pack (NoI,NoO)          -- or input NoI, or output NoO

instance Category Gui where
  id = noGui
  (.) = inNew2 (\ (_,c) (a,_) -> (a,c))

instance ProductCat Gui where
  exl = noGui
  exr = noGui
  (&&&) = inNew2 (\ (a,c) (a',d) -> (a `mappend` a', c `PairO` d))
