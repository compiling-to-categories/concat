{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

module Utils where

import ConCat.AltCat (toCcc)
import ConCat.Circuit ((:>), mkGraph, graphDot)
import ConCat.Syntactic (Syn,render)
import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Miscellany (GO)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden

type SynGr a b = (Syn a b, a :> b)

syngr :: (a -> b) -> SynGr a b
syngr f = (toCcc f, toCcc f)
{-# INLINE syngr #-}

-- | Run gold tests for a CCC'd syntax and circuit graph dot.
runSynCirc :: GO a b => String -> (a -> b) -> TestTree
runSynCirc nm f = runSynCirc' nm (syngr f)
{-# INLINE runSynCirc #-}

runSynCirc' :: GO a b => String -> SynGr a b -> TestTree
runSynCirc' nm (syn,circ) =
  testGroup nm
    [ gold "syn" (render syn)
    , gold "dot" (graphDot nm [] (mkGraph circ))
    ]
 where
   gold str = goldenVsString str
                     ("test/gold/" <> nm <> "-" <> str <> ".golden")
            . pure . pack
