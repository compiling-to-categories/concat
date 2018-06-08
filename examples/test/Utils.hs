{-# OPTIONS_GHC -Wall #-}

module Utils where

import qualified ConCat.AltCat as A
import           ConCat.Circuit (mkGraph, graphDot)
import           ConCat.Syntactic (render)
import qualified Data.ByteString.Lazy.Char8 as BS
import           Data.Semigroup ((<>))
import           Miscellany (GO, EC)
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Golden


------------------------------------------------------------------------------
-- | Run gold tests for a CCC'd syntax and circuit graph dot.
runSynCirc :: GO a b => String -> EC a b -> TestTree
runSynCirc nm (syn A.:**: circ) =
  testGroup nm
    [ gold "syn" (render syn)
    , gold "dot" (graphDot nm [] (mkGraph circ))
    ]
 where
   gold str = goldenVsString "syntax"
                     ("test/gold/" <> nm <> "-" <> str <> ".golden")
            . pure . BS.pack
