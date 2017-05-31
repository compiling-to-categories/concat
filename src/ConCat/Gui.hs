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

unFunO :: Out (a -> b) -> In a :* Out b
unFunO (a :--> b) = (a,b)
unFunO o = error ("unFunO: " ++ show o)

newtype Gui a b = Gui (Out (a -> b))

instance Newtype (Gui a b) where
  type O (Gui a b) = Out (a -> b)
  pack o = Gui o
  unpack (Gui o) = o

instance Category Gui where
  id = Gui (NoI :--> NoO)
  (unpack -> unFunO -> (_,c)) . (unpack -> unFunO -> (a,_)) =
    pack (a :--> c)
