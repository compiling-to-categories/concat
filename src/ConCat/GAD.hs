{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Generalized automatic differentiation

module ConCat.GAD where

import Prelude hiding (id,(.),curry,uncurry,const)
import qualified Prelude as P
import GHC.Exts (Coercible,coerce)

import GHC.Generics (Par1(..),(:.:)(..),(:*:)())
import Control.Newtype

import ConCat.Misc ((:*),inNew2,PseudoFun(..))
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow
import ConCat.Incremental
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Rep

newtype GD k a b = D { unD :: a -> b :* (a `k` b) }
-- data GD k a b = D { unD :: a -> b :* (a `k` b) }

-- Differentiable linear function, given the function and linear map version
linearD :: (a -> b) -> (a `k` b) -> GD k a b
-- linearD f f' = D (f &&& const f')
linearD f f' = D (\ a -> (f a, f'))
{-# INLINE linearD #-}

-- TODO: have linearD accept *just* the L version and convert via lapply

-- instance Newtype (D s a b) where
--   type O (D s a b) = (a -> b :* L s a b)
--   pack f = D f
--   unpack (D f) = f

instance HasRep (GD k a b) where
  type Rep (GD k a b) = (a -> b :* (a `k` b))
  abst f = D f
  repr (D f) = f

instance Category k => Category (GD k) where
  type Ok (GD k) = Ok k
  id = linearD id id
  D g . D f = D (\ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f'))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

--   (.) = inNew2 $ \ g f -> \ a ->
--     let (b,f') = f a
--         (c,g') = g b
--     in
--       (c, g' . f')

--   (.) = inNew2 $ \ g f -> second (uncurry (.)) . rassocP . first g . f

--   D g . D f = D $ \ a ->
--     let (b,f') = f a
--         (c,g') = g b
--     in
--       (c, g' . f')

instance ProductCat k => ProductCat (GD k) where
  exl = linearD exl exl
  exr = linearD exr exr
  D f &&& D g = D (\ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g'))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

--   (&&&) = inNew2 $ \ f g -> \ a ->
--     let (b,f') = f a
--         (c,g') = g a
--     in
--       ((b,c), f' &&& g')

--   (&&&) = inNew2 $ \ f g -> second (uncurry (&&&)) . transposeP . (f &&& g)

--   D f &&& D g = D $ \ a ->
--     let (b,f') = f a
--         (c,g') = g a
--     in
--       ((b,c), f' &&& g')

-- -- Don't define methods yet. I think I can optimize away the ClosedCat
-- -- operations in most cases. Once I'm happy with the results, define these methods and turn off the optimizations.
-- instance ClosedCat (GD k)

--     • No instance for (OpCon (Exp (GD k)) (Sat (Ok k)))
--         arising from the superclasses of an instance declaration
--     • In the instance declaration for ‘ClosedCat (GD k)’

{--------------------------------------------------------------------
    Other instances
--------------------------------------------------------------------}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

type D s = GD (L s)

type Inc = GD (-+>)

instance Num s => TerminalCat (D s) where
  it = linearD (const ()) zeroLM
  {-# INLINE it #-}

instance Ok (L s) b => ConstCat (D s) b where
  const b = D (const (b, zeroLM))
  {-# INLINE const #-}

instance TerminalCat Inc where
  -- it = linearD (const ()) zeroDelX
  -- it = D (const ((),constantDelX ()))
  it = const ()
  {-# INLINE it #-}

instance HasDelta b => ConstCat Inc b where
  const b = D (const (b, zeroDelX))
  {-# INLINE const #-}

-- TODO: Work on unifying more instances between D s and Inc.

instance Ok (L s) s => NumCat (D s) s where
  negateC = linearD negateC (scale (-1))
  addC    = linearD addC    jamLM
  mulC    = D (mulC &&& (\ (a,b) -> scale b `joinLM` scale a))
  powIC   = notDef "powC"
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

fullI1 :: (Atomic a, Atomic b) => (a -> b) -> Inc a b
fullI1 f = D (\ a -> (f a, atomic1 f a))

fullI2 :: (Atomic a, Atomic b, Atomic c) => (a :* b -> c) -> Inc (a :* b) c
fullI2 f = D (\ ab -> (f ab, atomic2 f ab))

instance (Atomic s, Num s) => NumCat Inc s where
  negateC = fullI1 negateC
  addC    = fullI2 addC
  subC    = fullI2 subC
  mulC    = fullI2 mulC
  powIC   = fullI2 powIC
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

const' :: (a -> c) -> (a -> b -> c)
const' = (const .)

scalarD :: Ok (L s) s => (s -> s) -> (s -> s -> s) -> D s s s
scalarD f d = D (\ x -> let r = f x in (r, scale (d x r)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' g when only x
-- matters.

scalarR :: Ok (L s) s => (s -> s) -> (s -> s) -> D s s s
scalarR f f' = scalarD f (\ _ -> f')
-- scalarR f x = scalarD f (const x)
-- scalarR f = scalarD f . const
{-# INLINE scalarR #-}

scalarX :: Ok (L s) s => (s -> s) -> (s -> s) -> D s s s
scalarX f f' = scalarD f (\ x _ -> f' x)
-- scalarX f f' = scalarD f (\ x y -> const (f' x) y)
-- scalarX f f' = scalarD f (\ x -> const (f' x))
-- scalarX f f' = scalarD f (const . f')
-- scalarX f f' = scalarD f (const' f')
-- scalarX f = scalarD f . const'
{-# INLINE scalarX #-}

square :: Num a => a -> a
square a = a * a
{-# INLINE square #-}

instance (Ok (L s) s, Fractional s) => FractionalCat (D s) s where
  recipC = scalarR recip (negate . square)
  {-# INLINE recipC #-}

instance (Ok (L s) s, Floating s) => FloatingCat (D s) s where
  expC = scalarR exp id
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
  {-# INLINE expC #-}
  {-# INLINE sinC #-}
  {-# INLINE cosC #-}

instance (RepCat (->) a r, RepCat k a r) => RepCat (GD k) a r where
  reprC = linearD reprC reprC
  abstC = linearD abstC abstC

#if 0
instance (Coercible a b, V s a ~ V s b, Ok2 k a b) => CoerceCat (GD k) a b where
  coerceC = linearD coerceC coerceC
#else
instance ( CoerceCat (->) a b
         , CoerceCat k a b
         ) => CoerceCat (GD k) a b where
  coerceC = linearD coerceC coerceC
#endif

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

andDeriv :: forall k a b . (a -> b) -> (a -> b :* (a `k` b))
andDeriv _ = error "andDeriv called"
{-# NOINLINE andDeriv #-}
{-# RULES "andDeriv" forall h. andDeriv h = unD (reveal (ccc h)) #-}
{-# ANN andDeriv PseudoFun #-}

-- The reveal greatly improved simplification and speeds up compilation.
-- Try removing, and retest.

deriv :: forall k a b . (a -> b) -> (a -> (a `k` b))
deriv _ = error "deriv called"
{-# NOINLINE deriv #-}
-- {-# RULES "deriv" forall h. deriv h = snd . andDeriv h #-}
-- {-# RULES "deriv" forall h. deriv h = snd P.. andDeriv h #-}
{-# RULES "deriv" forall h. deriv h = ccc (snd . andDeriv h) #-}
{-# ANN deriv PseudoFun #-}

-- 2016-01-07: The extra ccc helped with simplification.
-- Occassionally try without, and compare results.

andDer :: forall a b . (a -> b) -> (a -> b :* LR a b)
andDer = andDeriv
{-# NOINLINE andDer #-}
{-# RULES "andDer" andDer = andDeriv #-}
-- {-# ANN andDer PseudoFun #-}

der :: forall a b . (a -> b) -> (a -> LR a b)
der = deriv
{-# NOINLINE der #-}
{-# RULES "der" der = deriv #-}
-- {-# ANN der PseudoFun #-}

andInc :: forall a b . (a -> b) -> (a :* Delta a -> b :* Delta b)
andInc _ = error "andInc called"
{-# NOINLINE andInc #-}
{-# RULES "andInc" forall f. andInc f = flatInc (andDeriv f) #-}
-- {-# ANN andInc PseudoFun #-}

flatInc :: (a -> b :* (a -+> b)) -> (a :* Delta a -> b :* Delta b)
flatInc f (a,da) = (b, d da) where (b,DelX d) = f a

inc :: forall a b . (a -> b) -> (a :* Delta a -> Delta b)
inc _ = error "inc called"
{-# NOINLINE inc #-}
{-# RULES "inc" forall f. inc f = snd P.. andInc f #-}
-- {-# RULES "inc" forall f. inc f = uncurry (unDelX P.. snd P.. andInc f) #-}
-- {-# ANN inc PseudoFun #-}
