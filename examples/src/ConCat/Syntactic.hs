{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-} -- TEMP
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- {-# LANGUAGE DataKinds #-}  -- TEMP
{-# OPTIONS_GHC -Wno-unused-foralls -Wno-redundant-constraints #-} -- TEMP

-- #define ShowTypes

-- | Syntactic CCC

module ConCat.Syntactic where

import Prelude hiding (id,(.),lookup,const)

import Data.Tree (Tree(..))
import Data.Map (Map,fromList,lookup)
import Data.Foldable (toList)
import Text.PrettyPrint.HughesPJClass hiding (render,first)
import Data.Typeable (Typeable)
import Data.Constraint (Dict(..),(:-)(..))  -- temp
import Data.Key (Zip)
import GHC.TypeLits (KnownNat)

import Data.Functor.Rep (Representable(tabulate))
import qualified Data.Functor.Rep as R
import Data.Finite (Finite)
import Data.Vector.Sized (Vector)

import qualified ConCat.Category
import ConCat.AltCat
import ConCat.Misc (Unop)
import ConCat.Additive (Additive)
import ConCat.Rep
-- import ConCat.Finite

#ifdef ShowTypes
import ConCat.Misc (typeR)
#else
import ConCat.Misc (Yes1)
#endif

{--------------------------------------------------------------------
    Untyped S-expression
--------------------------------------------------------------------}

type DocTree = Tree PDoc

-- Using PDoc instead of String allows for complex values that can be
-- pretty-printed and parenthesized in context.
prettyTree :: DocTree -> PDoc
prettyTree (Node d [u,v]) p | Just (q,(lf,rf)) <- lookup nm fixities =
  maybeParens (p > q) $ sep [prettyTree u (lf q) <+> text nm, (prettyTree v) (rf q)]
 where nm = show (d 0)
prettyTree (Node f es) p =
  maybeParens (not (null es) && p > appPrec) $
  sep (f appPrec : map (\ e -> prettyTree e (appPrec+1)) es)

fixities :: Map String Fixity
fixities = fromList
  [ ("."  , (9,assocRight))
  , ("&&&", (3,assocRight))
  , ("***", (3,assocRight))
  , ("|||", (2,assocRight))
  , ("+++", (2,assocRight))
  ]

appt :: String -> [DocTree] -> DocTree
appt = Node . const . text
-- appt s ts = Node (const (text s)) ts

{--------------------------------------------------------------------
    Phantom-typed S-expression
--------------------------------------------------------------------}

newtype Syn a b = Syn DocTree

instance Show2 Syn where
  show2 = show

#if 1
-- instance Newtype (Syn a b) where
--   type O (Syn a b) = DocTree
--   pack s = Syn s
--   unpack (Syn s) = s

instance HasRep (Syn a b) where
  type Rep (Syn a b) = DocTree
  abst s = Syn s
  repr (Syn s) = s

atom :: Pretty a => a -> Syn a b
atom a = abst (Node (ppretty a) [])

app0 :: String -> Syn a b
app0 s = abst (appt s [])

app1 :: String -> Syn a b -> Syn c d
app1 s = inAbst (\ p -> appt s [p])

app2 :: String -> Syn a b -> Syn c d -> Syn e f
app2 s = inAbst2 (\ p q -> appt s [p,q])

apps :: (Functor h, Foldable h) => String -> h (Syn a b) -> Syn c d
apps s (fmap repr -> ts) = abst (appt s (toList ts))

#else

atom :: Pretty a => a -> Syn a b
atom a = Syn (Node (ppretty a) [])

app0 :: String -> Syn a b
app0 s = Syn (appt s [])

app1 :: String -> Syn a b -> Syn c d
app1 s (Syn p) = Syn (appt s [p])

app2 :: String -> Syn a b -> Syn c d -> Syn e f
app2 s (Syn p) (Syn q) = Syn (appt s [p,q])

unSyn :: Syn a b -> DocTree
unSyn (Syn t) = t

apps :: (Functor h, Foldable h) => String -> h (Syn a b) -> Syn c d
apps s (fmap unSyn -> ts) = Syn (appt s (toList ts))

#endif

instance Show (Syn a b) where show = render

render :: Syn a b -> String
render (Syn synu) = renderStyle (Style PageMode 80 1) (prettyTree synu 0)
{-# NOINLINE render #-}

-- NOINLINE here avoids the empty-case problem that was plaguing me.
-- Perhaps a strictness-based optimization forced my ccc definition.
-- 
-- I think I've fixed the empty-case issue via ConCat.Misc.oops. I still like
-- the NOINLINE for keeping the generated code simple.

-- #define INLINER(nm) {-# INLINE nm #-}
#define INLINER(nm) {-# NOINLINE nm #-}
-- #define INLINER(nm)

instance Category Syn where
  id  = app0 "id"
  (.) = app2 "."
  INLINER(id)
  INLINER((.))

instance AssociativePCat Syn where
  lassocP = app0 "lassocP"
  rassocP = app0 "rassocP"
  INLINER(lassocP)
  INLINER(rassocP)

instance MonoidalPCat Syn where
  (***)  = app2 "***"
  first  = app1 "first"
  second = app1 "second"
  INLINER((***))
  INLINER(first)
  INLINER(second)

instance BraidedPCat Syn where
  swapP = app0 "swapP"
  INLINER(swapP)

instance ProductCat Syn where
  exl = app0 "exl"
  exr = app0 "exr"
  dup = app0 "dup"
  -- (&&&)   = app2 "&&&"
  INLINER(exl)
  INLINER(exr)
  INLINER(dup)
  -- INLINER((&&&))

instance UnitCat Syn where
  lunit   = app0 "lunit"
  runit   = app0 "runit"
  lcounit = app0 "lcounit"
  rcounit = app0 "rcounit"
  INLINER(lunit)
  INLINER(runit)
  INLINER(lcounit)
  INLINER(rcounit)

instance TerminalCat Syn where
  it = app0 "it"
  INLINER(it)

instance AssociativeSCat Syn where
  lassocS = app0 "lassocS"
  rassocS = app0 "rassocS"
  INLINER(lassocS)
  INLINER(rassocS)

instance BraidedSCat Syn where
  swapS   = app0 "swapS"
  INLINER(swapS)

instance MonoidalSCat Syn where
  (+++) = app2 "+++"
  left    = app1 "left"
  right   = app1 "right"
  INLINER((+++))
  INLINER(left)
  INLINER(right)

instance CoproductCat Syn where
  inl = app0 "inl"
  inr = app0 "inr"
  jam = app0 "jam"
  INLINER(inl)
  INLINER(inr)
  -- (|||)   = app2 "|||"
  -- INLINER((|||))

instance CoproductPCat Syn where
  inlP   = app0 "inlP"
  inrP   = app0 "inrP"
  jamP   = app0 "jamP"
  -- swapPS = swapP
  INLINER(inlP)
  INLINER(inrP)
  INLINER(jamP)
  -- INLINER(swapPS)
  
instance DistribCat Syn where
  distl = app0 "distl"
  distr = app0 "distr"
  INLINER(distl)
  INLINER(distr)

instance ClosedCat Syn where
  apply   = app0 "apply"
  curry   = app1 "curry"
  uncurry = app1 "uncurry"
  INLINER(apply)
  INLINER(curry)
  INLINER(uncurry)

#if 1

atomicConst :: Show b => b -> Syn a b
atomicConst b = app1 "const" (app0 (show b))

#define LitConst(ty) \
instance ConstCat Syn (ty) where { const = atomicConst ; INLINER(const) }

LitConst(())
LitConst(Bool)
LitConst(Int)
LitConst(Integer)
LitConst(Float)
LitConst(Double)

#if 0
LitConst(Finite n)

instance (ConstCat Syn a, Show a, KnownNat n) => ConstCat Syn (Vector n a) where
  const = atomicConst
  INLINER(const)
#else
instance KnownNat n => ConstCat Syn (Finite n) where
  const = atomicConst
  INLINER(const)

instance (ConstCat Syn a, Show a, KnownNat n) => ConstCat Syn (Vector n a) where
  const = atomicConst
  INLINER(const)
#endif

-- instance Show a => ConstCat Syn (Vector n a) where ...

-- instance (ConstCat Syn a, ConstCat Syn b) => ConstCat Syn (a :* b) where
--   const = pairConst

#else

instance Pretty b => ConstCat Syn b where
  const b = app1 "const" (atom b)
  INLINER(const)
  -- unitArrow b = app1 "unitArrow" (atom (showPrec appPrec b))
  -- INLINER(unitArrow)

#endif

-- Some or all of the methods below are failing to inline

instance BoolCat Syn where
  notC = app0 "notC"
  andC = app0 "andC"
  orC  = app0 "orC"
  xorC = app0 "xorC"
  INLINER(notC)
  INLINER(andC)
  INLINER(orC)
  INLINER(xorC)

instance EqCat Syn a where
  equal    = app0 "equal"
  notEqual = app0 "notEqual"
  INLINER(equal)
  INLINER(notEqual)

instance Ord a => OrdCat Syn a where
  lessThan = app0 "lessThan"
  greaterThan = app0 "greaterThan"
  lessThanOrEqual = app0 "lessThanOrEqual"
  greaterThanOrEqual = app0 "greaterThanOrEqual"
  INLINER(lessThan)
  INLINER(greaterThan)
  INLINER(lessThanOrEqual)
  INLINER(greaterThanOrEqual)

instance MinMaxCat Syn a where
  minC = app0 "minC"
  maxC = app0 "maxC"

instance EnumCat Syn a where
  succC = app0 "succC"
  predC = app0 "predC"
  INLINER(succC)
  INLINER(predC)

instance NumCat Syn a where
  negateC = app0 "negateC"
  addC    = app0 "addC"
  subC    = app0 "subC"
  mulC    = app0 "mulC"
  powIC   = app0 "powIC"
  INLINER(negateC)
  INLINER(addC)
  INLINER(subC)
  INLINER(mulC)
  INLINER(powIC)

instance IntegralCat Syn a where
  divC = app0 "divC"
  modC = app0 "modC"
  INLINER(divC)
  INLINER(modC)

instance FractionalCat Syn a where
  recipC  = app0 "recipC"
  divideC = app0 "divideC"
  INLINER(recipC)
  INLINER(divideC)

instance RealFracCat Syn a b where
  floorC    = app0 "floorC"
  ceilingC  = app0 "ceilingC"
  truncateC = app0 "truncateC"
  INLINER(floorC)
  INLINER(ceilingC)
  INLINER(truncateC)

instance FloatingCat Syn a where
  expC = app0 "expC"
  cosC = app0 "cosC"
  sinC = app0 "sinC"
  logC = app0 "logC"
  INLINER(expC)
  INLINER(cosC)
  INLINER(sinC)
  INLINER(logC)

instance FromIntegralCat Syn a b where
  fromIntegralC = app0 "fromIntegralC"
  INLINER(fromIntegralC)

instance BottomCat Syn a b where
  bottomC = app0 "bottomC"
  INLINER(bottomC)

#if 1
instance IfCat Syn a where
  ifC = app0 "ifC"
  INLINER(ifC)
#else

atomicIf :: Syn a b
atomicIf = app0 "ifC"

#define LitIf(ty) \
instance IfCat Syn (ty) where { ifC = atomicIf ; INLINER(ifC) }

-- LitIf(())
LitIf(Bool)
LitIf(Int)
LitIf(Float)
LitIf(Double)

instance IfCat Syn () where ifC = unitIf

instance (IfCat Syn a, IfCat Syn b) => IfCat Syn (a :* b) where
  ifC = prodIf

#define AbstIf(abs) \
instance (IfCat Syn (Rep (abs)), T (abs), T (Rep (abs))) => IfCat Syn (abs) where { ifC = repIf }

AbstIf(Maybe a)
AbstIf((a,b,c))
...

#endif

instance UnknownCat Syn a b where
  unknownC = app0 "unknownC"
  INLINER(unknownC)

#ifdef ShowTypes
type T a = Typeable a

addTy :: forall t. Typeable t => Unop String
addTy = flip (++) (" :: " ++ show (typeR @t))

#else
type T = Yes1
addTy :: forall t. Unop String
addTy = id
#endif

app0' :: forall a b. (T a, T b) => String -> Syn a b
app0' = app0 . addTy @(a -> b)

instance (r ~ Rep a, T a, T r) => RepCat Syn a r where
  reprC = app0' "repr"
  abstC = app0' "abst"
  INLINER(reprC)
  INLINER(abstC)

instance (Typeable a, Typeable b) => CoerceCat Syn a b where
  coerceC = app0' "coerce"
  INLINER(coerceC)

instance OkIxProd Syn h where okIxProd = Entail (Sub Dict)

instance (Functor h, Foldable h
          {- OkIxProd Syn h, Representable h, Foldable h, Show (R.Rep h) -})
      => IxMonoidalPCat Syn h where
  crossF :: forall a b. Ok2 Syn a b => h (a `Syn` b) -> (h a `Syn` h b)
  crossF = apps "crossF"

instance (OkIxProd Syn h, Representable h, Foldable h, Show (R.Rep h))
      => IxProductCat Syn h where
  exF :: forall a . Ok Syn a => h (h a `Syn` a)
  exF = tabulate $ \ i -> app0 ("ex " ++ showsPrec 10 i "")
  replF :: forall a . Ok Syn a => a `Syn` h a
  replF = app0 "replF"

instance (OkIxProd Syn h, Representable h, Zip h, Traversable h, Show (R.Rep h))
      => IxCoproductPCat Syn h where
  inPF :: forall a. Ok Syn a => h (a `Syn` h a)
  inPF = tabulate $ \ i -> app0 ("inP " ++ showsPrec 10 i "")
  jamPF :: forall a. Ok Syn a => h a `Syn` a
  jamPF = app0 "jamPF"
  -- plusPF :: forall a b. Ok2 Syn a b => h (a `Syn` b) -> (h a `Syn` h b)
  -- plusPF = crossF

instance OkFunctor Syn h where okFunctor = Entail (Sub Dict)

instance Functor h => FunctorCat Syn h where
  fmapC  = app1 "fmap"
  unzipC = app0 "unzipC"
  INLINER(fmapC)
  INLINER(unzipC)

instance Zip h => ZipCat Syn h where
  zipC = app0 "zipC"
  INLINER(zipC)
  -- zipWithC = app0 "zipWithC"
  -- INLINER(zipWithC)

-- class OkFunctor k h => ZapCat k h where
--   zapC :: Ok2 k a b => h (a `k` b) -> (h a `k` h b)

-- instance ZapCat Syn h where
--   zapC = app0 "zapC"

instance {- Pointed h => -} PointedCat Syn h a where
  pointC = app0 "pointC"
  INLINER(pointC)

instance (Foldable h, Additive a) => AddCat Syn h a where
  sumAC = app0 "sumAC"
  INLINER(sumAC)

-- instance Functor h => Strong Syn h where
--   strength = app0 "strength"
--   INLINER(strength)

instance DistributiveCat Syn g f where
  distributeC = app0 "distributeC"
  INLINER(distributeC)

instance RepresentableCat Syn g where
  indexC    = app0 "indexC"
  tabulateC = app0 "tabulateC"
  INLINER(indexC)
  INLINER(tabulateC)

{--------------------------------------------------------------------
    Pretty-printing utilities
--------------------------------------------------------------------}

type Prec   = Rational
type Fixity = (Prec,Assoc)
type Assoc = (Prec -> Prec, Prec -> Prec)

assocLeft, assocRight, assocNone :: Assoc
assocLeft  = (id,succ)
assocRight = (succ,id)
assocNone  = (succ,succ)

-- Doc in a binding precedence context.
type PDoc = Prec -> Doc

-- Pretty-print with normal PrettyLevel.
-- We could include the PrettyLevel in PDoc instead.
ppretty :: Pretty a => a -> PDoc
ppretty a p = pPrintPrec prettyNormal p a

-- showPDoc :: Rational -> PDoc -> String
-- showPDoc p d = show (d p)

-- Precedence of function application.
-- Hack: use 11 instead of 10 to avoid extraneous parens when a function
-- application is the left argument of a function composition.
appPrec :: Prec
appPrec = 11 -- was 10
-- Revisit
