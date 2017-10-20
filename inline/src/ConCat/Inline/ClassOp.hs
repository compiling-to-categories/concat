{-# OPTIONS_GHC -Wall #-}

module ConCat.Inline.ClassOp where

-- | Magic function to inline a class-op, since @GHC.Exts.inline@ doesn't want to.
inline :: a -> a
inline x = x
{-# NOINLINE [0] inline #-}

-- TODO: Maybe augment inline to unfold non-class-ops. Or maybe better as is, so
-- we get more helpful failures.
