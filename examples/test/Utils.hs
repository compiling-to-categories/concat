{-# OPTIONS_GHC -Wall #-}

module Utils where

import ConCat.AltCat (toCcc)
import ConCat.Circuit (mkGraph, graphDot)
import ConCat.Syntactic (render)
import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Miscellany (GO)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden


------------------------------------------------------------------------------
-- | Run gold tests for a CCC'd syntax and circuit graph dot.
runSynCirc :: GO a b => String -> (a -> b) -> TestTree
runSynCirc nm f =
  testGroup nm
    [ gold "syn" (render (toCcc f))
    , gold "dot" (graphDot nm [] (mkGraph (toCcc f)))
    ]
 where
   gold str = goldenVsString str
                     ("test/gold/" <> nm <> "-" <> str <> ".golden")
            . pure . pack
{-# INLINE runSynCirc #-}
