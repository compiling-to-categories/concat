{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.ShowUtils
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Helpers for implementing Show instances
----------------------------------------------------------------------

module ConCat.ShowUtils
  ( showsPair
  , showsApp, showsApp1, showsApp2, appPrec, showSpaced, showsOp2, showsOp2'
  , OpInfo(..), HasOpInfo(..)
  , Prec, Assoc(..), Fixity
  , Show'(..)
  ) where

import Data.List (intersperse)

import ConCat.Misc (compose)

-- | Show for all type arguments. Unlike Show1 from Data.Functor.Classes, Show'
-- doesn't require Show for the type argument.
class Show' f where
  show'      ::        f a -> String
  showsPrec' :: Int -> f a -> ShowS
  showsPrec' _ x s = show' x ++ s
  show' x          = showsPrec' 0 x ""

showsPair :: (Show a, Show b) => Prec -> a -> b -> ShowS
showsPair _ a b = showParen True $
  showsPrec 0 a . showChar ',' . showsPrec 0 b

-- Simpler, but I don't like the resulting spaces around ",":
-- 
-- showsPair = showsOp2 True "," (-1,AssocNone)

data OpInfo = OpInfo String Fixity

class HasOpInfo p where
  opInfo :: p a -> Maybe OpInfo

-- | Show a simple function application
showsApp1 :: Show a => String -> Prec -> a -> ShowS
showsApp1 s p a = showParen (p > appPrec) $
                  showString s . showChar ' ' . showsPrec (appPrec+1) a

-- | Show a simple function application
showsApp2 :: (Show a, Show b) => String -> Prec -> a -> b -> ShowS
showsApp2 s p a b =
  showParen (p > appPrec) $
  showString s . showChar ' ' . showsPrec (appPrec+1) a . showChar ' ' . showsPrec (appPrec+1) b

-- | Show a simple function application
showsApp :: (Show a, Show b) => Prec -> a -> b -> ShowS
showsApp p a b = showParen (p >= appPrec) $
                 showsPrec (appPrec+1) a . showChar ' ' . showsPrec appPrec b

-- Precedence of function application.
-- Hack: use 11 instead of 10 to avoid extraneous parens when a function
-- application is the left argument of a function composition.
appPrec :: Int
appPrec = 11 -- was 10

-- TODO: Refactor showsApp & showsApp1
-- TODO: Resolve argument order

showSpaced :: [ShowS] -> ShowS
showSpaced = compose . intersperse (showChar ' ')

type Prec   = Int
data Assoc  = AssocLeft | AssocRight | AssocNone
type Fixity = (Prec,Assoc)

showsOp2 :: (Show a, Show b) => Bool -> String -> Fixity -> Prec -> a -> b -> ShowS
showsOp2 extraParens sop (p,assoc) q a b =
  showParen (q > p) $
    showSpaced
      [ showsPrec (lf p) a
      , showString sop
      , showsPrec (rf p) b
      ]
 where
   (lf,rf) = case assoc of
               AssocLeft  -> (incr, succ)
               AssocRight -> (succ, incr)
               AssocNone  -> (succ, succ)
   incr | extraParens = succ
        | otherwise   = id

showsOp2' :: (Show a, Show b) =>
             String -> Fixity -> Prec -> a -> b -> ShowS
showsOp2' = showsOp2 False -- no extra parens
