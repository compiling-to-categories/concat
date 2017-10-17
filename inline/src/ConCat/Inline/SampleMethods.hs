
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | 

-- ghc --show-iface SampleMethods.hi

{-# OPTIONS_GHC -ddump-simpl #-}
-- {-# OPTIONS_GHC -dverbose-core2core #-}
-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}
-- {-# OPTIONS_GHC -ddump-rules #-}

-- {-# OPTIONS_GHC -fplugin=ConCat.Inline.Plugin #-}

module ConCat.Inline.SampleMethods where

import ConCat.Inline.ClassOp (inline)

eq' :: Eq a => a -> a -> Bool
eq' = inline (==)
