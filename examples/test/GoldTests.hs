module GoldTests where

import Test.Tasty (defaultMain)
import BasicTests (basicTests)

main :: IO ()
main = do
  defaultMain basicTests

