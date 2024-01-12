{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

module Utils where

import qualified ConCat.AltCat as A
import           ConCat.Misc ((:*))
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
                     ("test/gold/" <> __GLASGOW_HASKELL_FULL_VERSION__ <> "/" <> nm <> "-" <> str <> ".golden")
            . pure . BS.pack

runDers :: (Show a, Show b, Show s) => String
  -> (a -> b :* (a -> b))
  -> (a -> b :* (b -> a))
  -> (a -> s :* a)
  -> a -> a -> b
  -> TestTree
runDers nm derf derr gradr a a' b =
 let gold str = goldenVsString str
                ("test/gold/" <> __GLASGOW_HASKELL_FULL_VERSION__ <> "/" <> nm <> "-" <> str <> ".golden")
                  . pure . BS.pack
     (b', d) = derf a
     (b'', rd) = derr a
     p = gradr a
 in
     testGroup nm
       [ gold "derf" (show (b', d a')),
         gold "derr" (show (b'', rd b)),
         gold "gradr" (show p) ]
{-# INLINE runDers #-}


