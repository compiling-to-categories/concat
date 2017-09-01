-- Attempt to recode the 2nd exercise from the Udacity Deep Learning
-- course from Python to Haskell, using the new machinery in concat.
--
-- Original author: David Banas <capn.freako@gmail.com>
-- Original date:   August 31, 2017
--
-- Copyright (c) 2017 David Banas; all rights reserved World wide.
-----------------------------------------------------------------------
-- To run:
--
--   stack build :tst-dl2
--
-- You might also want to use stack's --file-watch flag for automatic recompilation.

module Main where

import ConCat.AD   (gradient)
import ConCat.Misc (R)
import System.Directory (createDirectoryIfMissing)

f :: R -> R
f x = x * x + 2 * x + 1

f_name :: String
f_name = "x^2 + 2x + 1"

effectHaskell :: (Show a, Num a, Enum a, Show b) => String -> (a -> b) -> String
effectHaskell name func = unlines
  [ "The derivative of " ++ show f_name
  , "is producing the following input/output pairs:"
  , showFunc func
  , "You'll need to verify them."
  , "(Sorry, I'm not allowed to show you raw functions.)"
  ]

showFunc :: (Show a, Num a, Enum a, Show b) => (a -> b) -> String
showFunc f = show $ zip xs (map f xs)
  where xs = [0..2]

main :: IO ()
main = putStr $ effectHaskell f_name (gradient f)

