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

{-# LANGUAGE CPP             #-}
{-# LANGUAGE RecordWildCards #-}

{-# OPTIONS_GHC -Wall                   #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Main where

import Prelude hiding (readFile)

import Control.Arrow
import Data.Either
import Data.Vector.Random.Mersenne (random)
import qualified Data.Vector.Storable as VS
import qualified Data.Vector as V
import Data.Vector.Generic (convert, (!))
import System.Directory
import System.Random.Mersenne hiding (random)
import System.Random.Shuffle

import Codec.Picture
import Codec.Picture.Types

-- import ConCat.AD   (gradient)
-- import ConCat.Misc (R)
import ConCat.Classifier

#if 0
-- A simple experiment with automatic differentiation, as a pipe cleaner.
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

#else
-- The real McCoy.

-- | Given a training set and a test set, report the accuracy of test
-- set classification.
genOutput :: ([Img], [Lbl]) -> ([Img], [Lbl]) -> V.Vector Double -> String
genOutput (samps_trn, lbls_trn) (samps_tst, lbls_tst) rands = unlines
  [ "\n"
  -- , "Testing brute force classifier..."
  -- , "\tAfter training on " ++ show (length trn_set) ++ " sample points,"
  -- , "\tmy accuracy in classifying the test data is: " ++ show (accuracy bruteForce trn_set tst_set)
  -- , "Testing pre-averager classifier..."
  -- , "\tAfter training on " ++ show (length trn_set) ++ " sample points,"
  -- , "\tmy accuracy in classifying the test data is: " ++ show (accuracy averager trn_set tst_set)
  , "Testing simple gradient descent classifier..."
  , "\tAfter training on " ++ show (length trn_set) ++ " sample points,"
  , "\tmy accuracy in classifying the test data is: " ++ show (accuracy (sgd rands) trn_set tst_set)
  ]
    where trn_set    = precond $ zip samps_trn lbls_trn
          tst_set    = precond $ zip samps_tst lbls_tst
          precond    = map (first vnorm) . validate
          validate   = filter (not . or . first (V.any isNaN) . second (V.any isNaN))

main :: IO ()
main = do
  (inputs', labels') <- dataset  -- Yields Data.Vector.Storable.

  let inputs = map convert inputs'   -- Convert to Data.Vector.
      labels = map convert labels'

      trp      = length inputs * 70 `div` 100
      tep      = length inputs * 30 `div` 100

      -- training data
      trinputs = take trp inputs
      trlabels = take trp labels

      -- test data
      teinputs = take tep . drop trp $ inputs
      telabels = take tep . drop trp $ labels

  g <- newMTGen Nothing
  rands <- random g (V.length (head inputs) * V.length (head labels)) :: IO (V.Vector Double)
  print $ rands!0

  putStrLn $ genOutput (trinputs, trlabels) (teinputs, telabels) rands
#endif

-- | Found this code for reading in the notMNIST images, here:
-- https://github.com/mdibaiee/sibe/blob/master/examples/notmnist.hs
dataset :: IO ([VS.Vector Double], [VS.Vector Double])
dataset = do
  let dir = "notMNIST_small/"

  groups <- filter ((/= '.') . head) <$> listDirectory dir

  inputFiles <- mapM (listDirectory . (dir ++)) groups

  let n = 512 {-- minimum (map length inputFiles) --}
      numbers = map (`div` n) [0..n * length groups - 1]
      inputFilesFull = map (\(i, g) -> map ((dir ++ i ++ "/") ++) g) (zip groups inputFiles)


  inputImages <- mapM (mapM readImage . take n) inputFilesFull

  -- let names = map (take n) inputFilesFull

  -- let (l, r) = partitionEithers $ concat inputImages
  let (_, r) = partitionEithers $ concat inputImages
      inputs = map (fromPixels . convertRGB8) r
      labels = map (\i -> VS.replicate i 0 `VS.snoc` 1 VS.++ VS.replicate (9 - i) 0) numbers

      pairs  = zip inputs labels

  shuffled <- shuffleM pairs
  return (map fst shuffled, map snd shuffled)

  where
    fromPixels :: Image PixelRGB8 -> VS.Vector Double
    fromPixels img@Image { .. } =
      let pairs = [(x, y) | x <- [0..imageWidth - 1], y <- [0..imageHeight - 1]]
      in VS.fromList $ map iter pairs
      where
        iter (x, y) =
          let (PixelRGB8 r g b) = convertPixel $ pixelAt img x y
          in
            if r == 0 && g == 0 && b == 0 then 0 else 1

