{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Alternative interface to the class operations from ConCat.Category, so as
-- not to get inlined too eagerly to optimize.

module ConCat.AltCat where

{-# LANGUAGE NoMonomorphismRestriction #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP


import Prelude hiding (id,(.),curry,uncurry,const)

import ConCat.Category
  ( Category, Ok,Ok2,Ok3,Ok4,Ok5
  , ProductCat, Prod
  , CoproductCat, Coprod
  , ClosedCat, Exp
  )
import qualified ConCat.Category as C

#define Op(nm,ty) \
id :: ty; \
nm = C.nm ;\
{-# NOINLINE [2] nm #-}

-- id :: (Category k, Ok k a) => a `k` a
-- id = C.id
-- {-# NOINLINE [2] id    #-}

Op(id,(Category k, Ok k a) => a `k` a)

infixr 9 .
(.) :: forall k b c a. (Category k, Ok3 k a b c) => (b `k` c) -> (a `k` b) -> (a `k` c)
(.) = (C..)
{-# NOINLINE [2] (.)   #-}


exl :: (ProductCat k, Ok2 k a b) => Prod k a b `k` a
exl = C.exl
{-# NOINLINE [2] exl #-}

exr :: (ProductCat k, Ok2 k a b) => Prod k a b `k` b
exr = C.exr
{-# NOINLINE [2] exr #-}

infixr 3 ***, &&&

(&&&) :: forall k a c d. (ProductCat k, Ok3 k a c d)
      => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)
(&&&) = (C.&&&)
{-# NOINLINE [2] (&&&) #-}

(***) :: forall k a b c d. (ProductCat k, Ok4 k a b c d)
      => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
(***) = (C.***)
{-# NOINLINE [2] (***) #-}


infixr 2 +++, |||

inl :: (CoproductCat k, Ok2 k a b) => a `k` Coprod k a b
inl = C.inl
{-# NOINLINE [2] inl #-}

inr :: (CoproductCat k, Ok2 k a b) => b `k` Coprod k a b
inr = C.inr
{-# NOINLINE [2] inr #-}

(|||) :: forall k a c d. (CoproductCat k, Ok3 k a c d)
      => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)
(|||) = (C.|||)
{-# NOINLINE [2] (|||) #-}

(+++) :: forall k a b c d. (CoproductCat k, Ok4 k a b c d)
      => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b)
(+++) = (C.+++)
{-# NOINLINE [2] (+++) #-}


apply :: forall k a b. (ClosedCat k, Ok2 k a b) => Prod k (Exp k a b) a `k` b
apply = C.apply
{-# NOINLINE [2] apply #-}

curry :: (ClosedCat k, Ok3 k a b c) => (Prod k a b `k` c) -> (a `k` Exp k b c)
curry = C.curry
{-# NOINLINE [2] curry #-}

uncurry :: forall k a b c. (ClosedCat k, Ok3 k a b c)
        => (a `k` Exp k b c)  -> (Prod k a b `k` c)
uncurry = C.uncurry
{-# NOINLINE [2] uncurry #-}
