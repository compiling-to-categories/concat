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
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- {-# LANGUAGE DataKinds #-}  -- TEMP
{-# OPTIONS_GHC -Wno-unused-foralls -Wno-redundant-constraints #-} -- TEMP

-- | Syntactic CCC

-- #define VectorSized

module ConCat.Syntactic where

import Prelude hiding (id,(.),lookup,const)

import Data.Tree (Tree(..))
import Data.Map (Map,fromList,lookup)
import Control.Newtype
import Text.PrettyPrint.HughesPJClass hiding (render,first)
import Data.Typeable (Typeable)
import Data.Constraint (Dict(..),(:-)(..))  -- temp

#ifdef VectorSized
import GHC.TypeLits (KnownNat)
import Data.Finite (Finite)
#endif

import ConCat.Category
import ConCat.Misc (inNew,inNew2,Unop,Binop,typeR,Yes1,(:*))
import ConCat.Rep

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

#if 0
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
#else

atom :: Pretty a => a -> Syn a b
atom a = Syn (Node (ppretty a) [])

app0 :: String -> Syn a b
app0 s = Syn (appt s [])

app1 :: String -> Syn a b -> Syn c d
app1 s (Syn p) = Syn (appt s [p])

app2 :: String -> Syn a b -> Syn c d -> Syn e f
app2 s (Syn p) (Syn q) = Syn (appt s [p,q])

#endif

-- instance Show (Syn a b) where show = render

render :: Syn a b -> String
render (Syn synu) = renderStyle (Style PageMode 80 1) (prettyTree synu 0)
{-# NOINLINE render #-}

-- NOINLINE here avoids the empty-case problem that was plaguing me.
-- Perhaps a strictness-based optimization forced my ccc definition.
-- 
-- I think I've fixed the empty-case issue via ConCat.Misc.oops. I still like
-- the NOINLINE for keeping the generated code simple.

#define INLINER(nm) {-# INLINE nm #-}
-- #define INLINER(nm)

instance Category Syn where
  id  = app0 "id"
  (.) = app2 "."
  INLINER(id)
  INLINER((.))

instance ProductCat Syn where
  exl     = app0 "exl"
  exr     = app0 "exr"
  (&&&)   = app2 "&&&"
  (***)   = app2 "***"
  swapP   = app0 "swapP"
  first   = app1 "first"
  second  = app1 "second"
  lassocP = app0 "lassocP"
  rassocP = app0 "rassocP"
  INLINER(exl)
  INLINER(exr)
  INLINER((&&&))
  INLINER((***))
  INLINER(swapP)
  INLINER(first)
  INLINER(second)
  INLINER(lassocP)
  INLINER(rassocP)

instance TerminalCat Syn where
  it = app0 "it"
  INLINER(it)

instance CoproductCat Syn where
  inl     = app0 "inl"
  inr     = app0 "inr"
  (|||)   = app2 "|||"
  (+++)   = app2 "+++"
  jam     = app0 "jam"
  swapS   = app0 "swapS"
  left    = app1 "left"
  right   = app1 "right"
  lassocS = app0 "lassocS"
  rassocS = app0 "rassocS"
  INLINER(inl)
  INLINER(inr)
  INLINER((|||))
  INLINER((+++))
  INLINER(swapS)
  INLINER(left)
  INLINER(right)
  INLINER(lassocS)
  INLINER(rassocS)
  
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
LitConst(Float)
LitConst(Double)

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

instance OrdCat Syn a where
  lessThan = app0 "lessThan"
  greaterThan = app0 "greaterThan"
  lessThanOrEqual = app0 "lessThanOrEqual"
  greaterThanOrEqual = app0 "greaterThanOrEqual"
  INLINER(lessThan)
  INLINER(greaterThan)
  INLINER(lessThanOrEqual)
  INLINER(greaterThanOrEqual)

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
  INLINER(expC)
  INLINER(cosC)
  INLINER(sinC)

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

#ifdef VectorSized
instance KnownNat n => ArrayCat Syn n b where
  arrAt = app0 "arrAt"
  array = app0 "array"
  -- at    = app0 "at"
#else
instance ArrayCat Syn a b where
  arrAt = app0 "arrAt"
  array = app0 "array"
  -- at    = app0 "at"
#endif

instance UnknownCat Syn a b where
  unknownC = app0 "unknownC"
  INLINER(unknownC)

-- #define ShowTypes

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
  reprC = app0' "reprC"
  abstC = app0' "abstC"
  INLINER(reprC)
  INLINER(abstC)

instance (Typeable a, Typeable b) => CoerceCat Syn a b where
  coerceC = app0' "coerceC"
  INLINER(coerceC)

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
