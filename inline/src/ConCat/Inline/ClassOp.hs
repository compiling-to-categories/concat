
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

module ConCat.Inline.ClassOp where

import qualified GHC.Exts as X

-- | Magic function to inline a class-op, since 'X.inline' doesn't want to.
inline :: a -> a
inline x = x
{-# NOINLINE [0] inline #-}
