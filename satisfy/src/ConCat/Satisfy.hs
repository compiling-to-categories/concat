{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Magic function interface to ConCat.Satisfy.Plugin

module ConCat.Satisfy where

-- | Magic function to satisfy a constraint. Requires -fplugin=ConCat.Satisfy.Plugin to work.
satisfy :: forall c z. (c => z) -> z
satisfy = error "satisfy: Use -fplugin=ConCat.Satisfy.Plugin"
{-# NOINLINE [0] satisfy #-}

satisfy1 :: forall c f a. (c f => f a) -> f a
satisfy1 = satisfy @(c f)
{-# INLINE satisfy1 #-}

satisfy2 :: forall c f a b. (c f => f a b) -> f a b
satisfy2 = satisfy @(c f)
{-# INLINE satisfy2 #-}
