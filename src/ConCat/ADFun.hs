{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation using functions instead of linear maps

module ConCat.ADFun where

import Prelude hiding (id,(.),Float,Double)
import Control.Newtype

import ConCat.Misc ((:*),inNew2,PseudoFun(..))
import ConCat.Float

-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat hiding (const)

-- newtype D a b = D { unD :: a -> b :* (a -> b) }
-- newtype D a b = D (a -> b :* (a -> b))
data D a b = D (a -> b :* (a -> b))
-- data D a b = D { unD :: a -> b :* (a -> b) }

-- TODO: revert to newtype, and fix Plugin to handle it correctly.

unD :: D a b -> (a -> b :* (a -> b))
unD (D f) = f
{-# INLINE unD #-}

-- TODO: generalize from LM to any cartesian category

-- Differentiable linear function
linearD :: (a -> b) -> D a b
linearD f = D (f &&& const f)
{-# INLINE linearD #-}

instance Newtype (D a b) where
  type O (D a b) = a -> b :* (a -> b)
  pack = D
  unpack = unD

instance Category D where
  id = linearD id
  D g . D f = D (\ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f'))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance ProductCat D where
  exl = linearD exl
  exr = linearD exr
  D f &&& D g = D (\ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g'))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

-- TODO: use $ in (.) and (&&&) definitions.
-- My compiler plugin was struggling with ($) in case scrutinees.

-- -- Don't define methods yet. I think I can optimize away the ClosedCat
-- -- operations in most cases. Once I'm happy with the results, define these
-- -- methods and turn off the optimizations.
-- instance ClosedCat D where
--   -- apply = D (\ (f,a) -> (f a, \ (df,da) -> undefined))

--     • No instance for (OpCon (Exp D) (Sat (OkLM s)))
--         arising from the superclasses of an instance declaration
--     • In the instance declaration for ‘ClosedCat D’

#if 0

applyD :: D (D a b :* a) b
applyD = D (\ (D h, a) ->
              let (b,b') = h a in
                (b,\ (df,da) -> df a + undefined)
           )

a :: a
D h :: D a b
h :: a -> b :* (a -> b)
(b,b') :: b :* (a -> b)
b :: b
b' :: a -> b

want :: D a b :* a -> b
#endif

{--------------------------------------------------------------------
    Other instances
--------------------------------------------------------------------}

instance TerminalCat D where
  it = linearD (const ())
  {-# INLINE it #-}

instance Num b => ConstCat D b where
  const b = D (const (b, const 0))
  {-# INLINE const #-}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

instance Num a => NumCat D a where
  negateC = linearD negateC
  addC    = linearD addC
  mulC    = D (mulC &&& (\ (a,b) (da,db) -> da*b + db*a))
  powIC   = notDef "powC"
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

const' :: (a -> c) -> (a -> b -> c)
const' f a _b = f a
-- const' = (const .)
{-# INLINE const' #-}

scalarD :: Num s => (s -> s) -> (s -> s -> s) -> D s s
scalarD f der = D (\ x -> let r = f x in (r, (der x r *)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' g when only x
-- matters.

scalarR :: Num s => (s -> s) -> (s -> s) -> D s s
scalarR f = scalarD f . const
{-# INLINE scalarR #-}

scalarX :: Num s => (s -> s) -> (s -> s) -> D s s
-- scalarX f = scalarD f . const'
scalarX f f' = scalarD f (const' f')  -- better inlining
{-# INLINE scalarX #-}

square :: Num a => a -> a
square a = a * a
{-# INLINE square #-}

instance Fractional s => FractionalCat D s where
  recipC = scalarR recip (negate . square)
  {-# INLINE recipC #-}

instance Floating s => FloatingCat D s where
  expC = scalarR exp id
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
  {-# INLINE expC #-}
  {-# INLINE sinC #-}
  {-# INLINE cosC #-}

{--------------------------------------------------------------------
    Sampling on a basis
--------------------------------------------------------------------}

-- Temporary hack until I'm using functors

class HasZero a where
  zero :: a

instance HasZero Float  where zero = 0; {-# INLINE zero #-}
instance HasZero Double where zero = 0; {-# INLINE zero #-}
instance (HasZero a, HasZero b) => HasZero (a :* b) where
  zero = (zero,zero)
  {-# INLINE zero #-}

class HasZero a => HasBasis a r where
  type B a r
  onBasis :: (a -> r) -> B a r

instance HasBasis Float r where
  type B Float r = r
  onBasis f = f 1
  {-# INLINE onBasis #-}

instance HasBasis Double r where
  type B Double r = r
  onBasis f = f 1
  {-# INLINE onBasis #-}

instance (HasBasis a r, HasBasis b r) => HasBasis (a :* b) r where
  type B (a :* b) r = B a r :* B b r
  onBasis f = (onBasis (f . (,zero)), onBasis (f . (zero,)))
  {-# INLINE onBasis #-}

{--------------------------------------------------------------------
    Utilities
--------------------------------------------------------------------}

dfun :: (a -> b) -> (a -> b :* (a -> b))
dfun _ = error "dfun called"
{-# NOINLINE dfun #-}
{-# RULES "dfun" forall h. dfun h = unD' (reveal (ccc h)) #-}
{-# ANN dfun PseudoFun #-}

dsc :: Num a => (a -> b :* (a -> b)) -> (a -> b :* b)
-- dsc f a = (b,b' 1) where (b,b') = f a
-- dsc f = second (`id` 1) . f
dsc f = \ a -> let (b,b') = f a in (b, b' 1)
{-# INLINE dsc #-}

da2b2 :: (a -> b :* (a -> b)) -> (a :* a -> b :* b)
da2b2 f = \ (a,da) -> let (b,b') = f a in (b, b' da)
{-# INLINE da2b2 #-}

dbas :: HasBasis a b => (a -> b :* (a -> b)) -> (a -> b :* B a b)
dbas f = \ a -> let (b,b') = f a in (b, onBasis b')
{-# INLINE dbas #-}

unD' :: D a b -> a -> b :* (a -> b)
-- unD' (D f) = f
#if 0
unD' d = unD d
-- {-# INLINE unD' #-}
-- {-# INLINE [2] unD' #-}
{-# INLINE [0] unD' #-}
#else
unD' _ = error "unD' called"
{-# NOINLINE unD' #-}
{-# RULES "unD'" [0] unD' = unD #-}
#endif

-- Experiment: inline on demand
{-# RULES "ccc of unD'" forall q. ccc (unD' q) = ccc (unD q) #-}
{-# RULES "unD' of D" forall f. unD' (D f) = f #-}

