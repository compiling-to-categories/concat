{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

-- | Bug(?) in Coercible constraint solving.
-- Filed https://ghc.haskell.org/trac/ghc/ticket/13083#ticket

import GHC.Generics (Par1(..),(:*:)(..))
import GHC.Exts (coerce)

-- Representation as free vector space
type family V (a :: *) :: * -> *

type instance V Float = Par1
type instance V (a,b) = V a :*: V b

type instance V (Par1 a) = V a
type instance V ((f :*: g) a) = V (f a, g a)

--     • Variable ‘a’ occurs more often
--         in the type family application ‘V (f a, g a)’
--         than in the instance head
--       (Use UndecidableInstances to permit this)

type R = Float

-- Linear map in row-major order
newtype L a b = L (V b (V a R))

-- Use coerce to drop newtype wrapper
bar :: L a b -> V b (V a R)
bar = coerce

{--------------------------------------------------------------------
    Bug demo
--------------------------------------------------------------------}

-- A rejected type specialization of bar with a ~ (R,R), b ~ (Par1 R,R)
foo :: L (R,R) (Par1 R,R) -> V (Par1 R,R) (V (R,R) R)
foo = coerce

--     • Couldn't match representation of type ‘V Par1’
--                                with that of ‘Par1’
--         arising from a use of ‘coerce’

-- Note that Par1 has the wrong kind (* -> *) for V Par1

-- Same error:
-- 
-- foo :: (a ~ (R,R), b ~ (Par1 R,R)) => L a b -> V b (V a R)

-- The following similar signatures work:

-- foo :: L (R,R) (R,Par1 R) -> V (R,Par1 R) (V (R,R) R)
-- foo :: L (Par1 R,R) (R,R) -> V (R,R) (V (Par1 R,R) R)

-- Same error:

-- -- Linear map in column-major order
-- newtype L a b = L (V a (V b s))

-- foo :: L (R,R) (Par1 R,R) -> V (R,R) (V (Par1 R,R) R)
-- foo = coerce
