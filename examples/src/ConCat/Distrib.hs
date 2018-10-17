{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | 

module ConCat.Distrib where

import Prelude hiding ((.))

import Data.Map (Map)
import qualified Data.Map as M

import ConCat.Misc (R)
import ConCat.AltCat
import qualified ConCat.Category

newtype Distrib a b = Distrib (a -> Map b R)

-- TODO: generalize Distrib to a category transformer

instance Category Distrib where
  type Ok Distrib = Ord
  id = Distrib (\ a -> M.singleton a 1)
  Distrib g . Distrib f = Distrib h
   where
     h a = M.unionsWith (+) [ (p *) <$> g b | (b,p) <- M.toList (f a) ]
