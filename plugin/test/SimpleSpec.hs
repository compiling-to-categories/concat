{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fdicts-strict #-}

module SimpleSpec where

import ConCat.AltCat (toCcc)
import Test.Hspec
import Types



spec :: Spec
spec = describe "test" $ do
  it "should compile" $
    CFloat 5 `shouldNotBe` toCcc (id @Float)

  it "should compile" $
    CFloat 5 `shouldNotBe` toCcc (double @Float)

double :: Num a => a -> a
double = \x -> x + x

