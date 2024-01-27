{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Class-op aliases that have been inlined to dictionary method accessors.
-- To see the effect,
--   ghc --show-iface SampleMethods.hi

-- {-# OPTIONS_GHC -ddump-simpl #-}
-- {-# OPTIONS_GHC -dverbose-core2core #-}
-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}
-- {-# OPTIONS_GHC -ddump-rules #-}

-- Haddock throws an exception if this plugin is enabled here.
#ifdef D__HADDOCK_VERSION__
{-# OPTIONS_GHC -fplugin=ConCat.Inline.Plugin #-}
#endif

module ConCat.Inline.SampleMethods where

import qualified Prelude as P
import ConCat.Inline.ClassOp (inline)

(==), (/=) :: P.Eq a => a -> a -> P.Bool
(==) = inline (P.==)
(/=) = inline (P./=)
