{-# OPTIONS_GHC -Wall #-}

-- | For importing qualfied by ConCat clients. Enables some rewrite rules and
-- Coercible instances. Unfortunately, doing so leads to warnings of unused
-- imports in the client module. How to resolve (without -Wno-unused-imports)?

module ConCat (module GHC.Generics) where

import GHC.Generics     -- needed to avoid coercion holes (sorry)

import ConCat.Rebox  () -- rewrite rules
import ConCat.AltCat () -- rewrite rules
