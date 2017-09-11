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
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE InstanceSigs               #-}

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

import Prelude hiding (zip, zipWith)

import Control.Arrow
import Data.Key (Zip(..))
-- import qualified Data.Vector.Storable as VS
-- import qualified Data.Vector.Generic as VG
import qualified Data.Vector as V

import ConCat.AD
import ConCat.Free.VectorSpace
import ConCat.GAD
import ConCat.GradientDescent

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
type Img = V.Vector Double  -- concatenation of pixel rows
type Lbl = V.Vector Double  -- N-element vector of label probabilities
-- type Img = V.Vector -- concatenation of pixel rows
-- type Lbl = V.Vector -- N-element vector of label probabilities

newtype ImgClassifier = ImgClassifier {runImgClassifier :: [(Img, Lbl)] -> Img -> Lbl}
instance Classifier ImgClassifier where
  type Sample ImgClassifier = Img
  type Label  ImgClassifier = Lbl
  type Acc    ImgClassifier = Double
  train                = runImgClassifier
  accuracy clf trn tst = fromIntegral (length matches) / fromIntegral (length tst)
    where matches  = filter (uncurry (==)) $ zip (map (V.maxIndex . snd) tst) res
          res      = map (V.maxIndex . train clf trn . fst) tst

-- | A naive image classifier, which just correlates a test image
-- against each image in the training set, to compute its label.
bruteForce = ImgClassifier train'

-- train' trn_set img = V.map (/ V.sum v) v
train' :: [(Img,Lbl)] -> Img -> Lbl
train' trn_set img = vprob v
  where v        = foldl func init_vec trn_set
        func     = flip (vadd . uncurry vscale . first (abs . vdot img))
        init_vec = V.replicate (V.length $ snd $ head trn_set) 0

-- | A presumed improvement over *bruteForce*, which pre-averages the
-- training images, according to label, before correlating against the
-- test image.
--
-- Testing shows no improvement over *BruteForce*.
averager = ImgClassifier train''

-- train'' trn_set img = V.map (/ V.sum v) v
train'' trn_set img = vprob v
  where v        = V.fromList $ map (foldl func 0.0) trn_set'
        func x   = (+ x) . abs . vdot img
        trn_set' = [ [fst x | x <- filter ((== n) . V.maxIndex . snd) trn_set]
                     | n <- [0..(V.length (snd $ head trn_set) - 1)]
                   ]

-- TODO: LMS approx., ala DFE, as pre-cursor to full blown SGD attempt?

-- | A first attempt at Simple Gradient Descent (SGD).
--
-- The intent here is to avoid actually writing code to find the
-- gradient and use Conal's automatic differentiation machinery,
-- instead.

-- An image classifier is (for now) a linear map from an image to a
-- label vector. As such, it must have:
-- - M "rows", where 'M' is the number of possible classifications, and
-- - N "columns", where 'N' is the length of an image vector (i.e. - flattened array.)

-- Start with a purely functional definition and use:
--   lmap :: forall s a b. (a -> b) -> L s a b
-- when the time comes, for Verilog implementation, etc.
type Clf = Img -> Lbl

cost :: [(Img,Lbl)] -> Clf -> Double
cost prs clf = sse (map snd prs) (map clf (map fst prs))

-- | Compute the sum of the squared magnitudes of the difference vectors.
--
-- Note: *sum* of squares is equivalent to *mean* of squares, as a cost
--       function, when all vectors are of equal length.
sse :: [Lbl] -> [Lbl] -> Double
-- sse = sum . zipWith (V.sum . V.map (\x -> x * x) . vsub)
-- sse = sum . zipWith (V.sum . (V.map (\x -> x * x) ((.) . (.)) vsub))
sse us vs = sum $ map (V.sum . V.map (\x -> x * x)) $ zipWith vsub us vs

-- class HasV s a where
--   type V s a :: * -> *
--   toV :: a -> V s a s
--   unV :: V s a s -> a

instance HasV s (V.Vector s) where
  type V s (V.Vector s) = V.Vector
  toV = id
  unV = id

instance Zip V.Vector where
  zipWith :: (a -> b -> c) -> V.Vector a -> V.Vector b -> V.Vector c
  zipWith = V.zipWith

-- instance Functor V.Vector where
--   fmap :: (a -> b) -> V.Vector a -> V.Vector b
--   fmap = V.map

sgd = ImgClassifier . train'''

-- maximizeL, minimizeL :: (HasV R a, Zip (V R a), Eq a) => R -> D R a R -> a -> [a]
-- type D s = GD (L s) (type D s a b = GD (L s) a b)
-- newtype L s a b = L ((V s a :-* V s b) s)
-- data GD k a b = D { unD :: a -> b :* (a `k` b) }
-- andDer :: forall k a b . (a -> b) -> (a -> b :* (a `k` b))
-- trn_set :: [(Img,Lbl)]
-- cost trn_set :: Clf -> Double
-- andDer (cost trn_set) :: Clf -> Double :* (Clf `k` Double) ~ D R Clf Double ~ GD (L R) Clf Double
gamma = 0.1

train''' rands trn_set = head $ drop 10 $ minimizeL gamma (D (andDer (cost trn_set))) initClf
  where initClf :: Clf
        initClf img = V.fromList [vdot img (V.take n (V.drop (n * i) rands)) | i <- [0..(m-1)]]
        n           = (V.length . fst . head) trn_set  -- length of image vector
        m           = (V.length . snd . head) trn_set  -- length of label vector

-- | Various needed vector utility functions not provided by Data.Vector.Storable.
vdot :: Num a => V.Vector a -> V.Vector a -> a
vdot v1 = V.sum . V.zipWith (*) v1

vscale :: Num a => a -> V.Vector a -> V.Vector a
vscale s = V.map (* s)

vadd :: Num a => V.Vector a -> V.Vector a -> V.Vector a
vadd = V.zipWith (+)

vsub :: Num a => V.Vector a -> V.Vector a -> V.Vector a
vsub = V.zipWith (-)

vmean :: (Num a, Fractional a) => V.Vector a -> a
vmean v = V.sum v / fromIntegral (V.length v)

-- | Normalize a vector to be bounded by [-0.5, +0.5] and have zero mean.
vnorm :: (Num a, Ord a, Fractional a) => V.Vector a -> V.Vector a
vnorm v = let v'  = vbias (-1.0 * vmean v) v
              rng = vrange v'
           in case rng of
                0.0 -> v'
                _   -> vscale (1.0 / rng) v'

vrange :: (Num a, Ord a) => V.Vector a -> a
vrange v = V.maximum v - V.minimum v

vbias :: (Num a) => a -> V.Vector a -> V.Vector a
vbias s = V.map (+ s)

vprob :: (Num a, Fractional a) => V.Vector a -> V.Vector a
vprob v = V.map (/ V.sum v) v

