{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators, GADTs, PatternGuards, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds, RankNTypes, CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ReificationRules.ToCCC
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert lambda expressions to CCC combinators
----------------------------------------------------------------------

module ReificationRules.ToCCC
  ( toCCC, toCCC'
  ) where

import Prelude hiding (id,(.),curry,uncurry,const)

import Control.Monad (mplus)
import Data.Maybe (fromMaybe)
-- import Data.Coerce (Coercible,coerce)

-- import Data.Proof.EQ
import Data.Type.Equality ((:~:)(..))

-- import Circat.Category
-- Sad hack. I don't yet know how to handle Loop generally enough.
-- See BiCCCC'.
-- TODO: rethink the whole extensibility thing.
-- import Circat.Circuit ((:>))

import ConCat.Category
import ConCat.Misc
-- import ConCat.Prim (Prim)
import ConCat.Exp

{--------------------------------------------------------------------
    Conversion
--------------------------------------------------------------------}

-- type BiCCCC' k p = BiCCCC k p
-- Sad hack. See above.
-- type BiCCCC' k p = (k ~ (:>), p ~ Prim)

type BiCCCC' (cat :: k -> k -> *) (p :: k -> *) = ClosedCat cat

-- type BiCCCC' cat (p :: * -> *) = (ClosedCat cat, Exp cat ~ (->))

-- | Rewrite a lambda expression via CCC combinators
toCCC :: BiCCCC' k p => E p a -> (() `k` a)
toCCC e = convert e UnitPat

-- toCCC :: forall p a. E p a -> forall k. BiCCCC' k p => (Unit `k` a)

-- | Convert @\ p -> e@ to CCC combinators
convert :: forall a b prim k. BiCCCC' k prim =>
           E prim b -> Pat a -> (a `k` b)
-- convert (ConstE x)   _ = unitArrow x . it
convert (Var v)      p = convertVar v p
convert (u :^ v)     p = apply . (convert u p &&& convert v p)
convert (Lam q e)    p = curry (convert e (p :$ q))
-- convert (Either f g) p = curry ((convert' f ||| convert' g) . distl)
--  where
--    convert' :: E prim (c :=> d) -> ((a :* c) `k` d)
--    convert' h = uncurry (convert h p)
-- convert (Loop h)     p = curry (loopC (uncurry (convert h p) . rassocP))
-- -- convert (CoerceE a)  p = coerceC . convert a p

-- TODO: Rewrite convert to share convert' and use for Either and Loop.
-- Maybe swap arguments for better partial application.

#if 0

-- For Loop, we have

p :: Pat u
Loop h :: E p (a -> b)
h :: E p (a :* s -> b :* s)

convert h p :: u `k` (a :* s :=> b :* s)

loopC :: ((a :* s) `k` (b :* s)) -> (a `k` b)

-- and we need

convert (Loop h) p :: u `k` (a :=> b)

-- One step at a time:

convert h p :: u `k` (a :* s :=> b :* s)
uncurry (convert h p) :: (u :* (a :* s)) `k` (b :* s)
uncurry (convert h p) . rassocP :: ((u :* a) :* s) `k` (b :* s)
loopC (uncurry (convert h p) . rassocP) :: (u :* a) `k` b
curry (loopC (uncurry (convert h p) . rassocP)) :: u `k` (a :=> b)

#endif

-- | Variant on 'toCCC'
toCCC' :: BiCCCC' k p => E p (a :=> b) -> (a `k` b)
toCCC' = unUnitFun . toCCC

-- toCCC' :: forall p a b. E p (a :=> b) -> forall k. BiCCCC' k p => (a `k` b)

-- TODO: Handle constants in a generic manner, so we can drop the constraint that k ~ (:->).

-- convert k (Case (a,p) (b,q) ab) =
--   (convert (k :$ a) p ||| convert (k :$ b) q) . ldistribS . (Id &&& convert k ab)

-- Convert a variable in context
convertVar :: forall b a k. ({- NatCat k,-} ProductCat k) =>
              V b -> Pat a -> (a `k` b)
convertVar u = fromMaybe (error $ "convert: unbound variable: " ++ show u) .
               conv
 where
   conv :: forall c. Pat c -> Maybe (c `k` b)
   conv (VarPat v) | Just Refl <- v ===? u = Just id
                   | otherwise             = Nothing
   conv UnitPat     = Nothing
   conv (p :$ q)    = ((. exr) <$> conv q) `mplus` ((. exl) <$> conv p)
   conv (p :@ q)    = conv q `mplus` conv p
--    conv ZeroPat     = Nothing
--    conv (SuccPat p) = (. predA) <$> conv p

-- Note that we try q before p. This choice cooperates with uncurrying and
-- shadowing.

-- Alternatively,
-- 
--    conv (p :$ q) = descend exr q `mplus` descend exl p
--     where
--       descend :: (c `k` d) -> Pat d -> Maybe (c `k` b)
--       descend sel r = (. sel) <$> conv r

