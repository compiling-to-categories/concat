-- Proper factoring of two "brute force" letter calssification experiments.
--
-- Original author: David Banas <capn.freako@gmail.com>
-- Original date:   September 6, 2017
--
-- Copyright (c) 2017 David Banas; all rights reserved World wide.
--
-- This module is the result of factoring out common code between two
-- source files:
-- - ud_dl_2.hs
-- - ud_dl_2A.hs

{-# LANGUAGE CPP                        #-}
-- {-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wall                   #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Classifier
-- Copyright   :  (c) 2017 David Banas
-- License     :  BSD3
--
-- Maintainer  :  capn.freako@gmail.com
-- Stability   :  experimental
--
-- Machine learning classifier representation.
----------------------------------------------------------------------

module ConCat.Classifier where

import Control.Arrow
import qualified Data.Vector.Storable as VS

-- | Something that knows how to train itself, to classify data.
class Classifier a where
  type Sample a :: *  -- type of data to be classified
  type Label  a :: *  -- type of classification label
  type Acc    a :: *  -- type of accuracy measure
  -- | Use a list of training pairs to produce a classification function.
  train    :: a -> [(Sample a, Label a)] -> Sample a              -> Label a
  -- | Measure our accuracy, given particular training/test data sets.
  accuracy :: a -> [(Sample a, Label a)] -> [(Sample a, Label a)] -> Acc a

-- | A classifier specific to images.
type Img = VS.Vector Double  -- concatenation of pixel rows
type Lbl = VS.Vector Double  -- N-element vector of label probabilities

newtype ImgClassifier = ImgClassifier {runImgClassifier :: [(Img, Lbl)] -> Img -> Lbl}
instance Classifier ImgClassifier where
  type Sample ImgClassifier = Img
  type Label  ImgClassifier = Lbl
  type Acc    ImgClassifier = Float
  train                = runImgClassifier
  accuracy clf trn tst = fromIntegral (length matches) / fromIntegral (length tst)
    where matches  = filter (uncurry (==)) $ zip (map (VS.maxIndex . snd) tst) res
          res      = map (VS.maxIndex . train clf trn . fst) tst

-- | A naive image classifier, which just correlates a test image
-- against each image in the training set, to compute its label.
bruteForce = ImgClassifier train'

train' trn_set img = VS.map (/ VS.sum v) v
  where v        = foldl func init_vec trn_set
        func     = flip (vadd . uncurry vscale . first (abs . vdot img))
        init_vec = VS.replicate (VS.length $ snd $ head trn_set) 0

-- | A presumed improvement over *bruteForce*, which pre-averages the
-- training images, according to label, before correlating against the
-- test image.
--
-- Testing shows no improvement over *BruteForce*.
averager = ImgClassifier train''

train'' trn_set img = VS.map (/ VS.sum v) v
  where v        = VS.fromList $ map (foldl func 0.0) trn_set'
        func x   = (+ x) . abs . vdot img
        trn_set' = [ [fst x | x <- filter ((== n) . VS.maxIndex . snd) trn_set]
                     | n <- [0..(VS.length (snd $ head trn_set) - 1)]
                   ]

-- | Various needed vector utility functions not provided by Data.Vector.Storable.
vdot :: (Num a, VS.Storable a) => VS.Vector a -> VS.Vector a -> a
vdot v1 = VS.sum . VS.zipWith (*) v1

vscale :: (Num a, VS.Storable a) => a -> VS.Vector a -> VS.Vector a
vscale s = VS.map (* s)

vadd :: (Num a, VS.Storable a) => VS.Vector a -> VS.Vector a -> VS.Vector a
vadd = VS.zipWith (+)

vmean :: (Num a, Fractional a, VS.Storable a) => VS.Vector a -> a
vmean v = VS.sum v / fromIntegral (VS.length v)

-- | Normalize a vector to be bounded by [-0.5, +0.5] and have zero mean.
vnorm :: (Num a, Ord a, Fractional a, VS.Storable a) => VS.Vector a -> VS.Vector a
vnorm v = let v'  = vbias (-1.0 * vmean v) v
              rng = vrange v'
           in case rng of
                0.0 -> v'
                _   -> vscale (1.0 / rng) v'

vrange :: (Num a, Ord a, VS.Storable a) => VS.Vector a -> a
vrange v = VS.maximum v - VS.minimum v

vbias :: (Num a, VS.Storable a) => a -> VS.Vector a -> VS.Vector a
vbias s = VS.map (+ s)

