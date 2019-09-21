{-# OPTIONS_GHC -Wall #-}

module Utils (GO, runSynCirc) where

import ConCat.AltCat (toCcc)
import ConCat.Circuit (GO, mkGraph, graphDot)
import ConCat.Syntactic (render)
import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import GHC.Exts (inline)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden

-- | Run gold tests for a CCC'd syntax and circuit graph dot.
runSynCirc :: GO a b => String -> (a -> b) -> TestTree
runSynCirc nm f =
  testGroup nm
    [ gold "syn" (render (toCcc (inline f)))
    , gold "dot" (graphDot nm [] (mkGraph (toCcc (inline f))))
    ]
 where
   gold str = goldenVsString str
                     ("test/gold/" <> nm <> "-" <> str <> ".golden")
            . pure . pack
{-# INLINE runSynCirc #-}

-- Without the explicit inline applications above, some tests fail.
-- I think GHC is normally reluctant to duplicate code.
