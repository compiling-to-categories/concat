{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Syntactic CCC

module ConCat.Syntactic where

import Prelude hiding (id,(.),lookup,Float,Double)

import Data.Map (Map,fromList,lookup)
import Control.Newtype
import Text.PrettyPrint.HughesPJ hiding (render)

import ConCat.Category
import ConCat.Misc ((:*),inNew,inNew2,Unop,Binop)
import ConCat.Float (Float,Double)

{--------------------------------------------------------------------
    Untyped S-expression
--------------------------------------------------------------------}

data SynU = SynU String [SynU] deriving Show

atomu :: String -> SynU
atomu s = SynU s []

app1u :: String -> Unop SynU
app1u s p = SynU s [p]

app2u :: String -> Binop SynU
app2u s p q = SynU s [p,q]

-- TODO: use the Pretty class from Text.PrettyPrint.HughesPJClass

prettyu :: SynU -> PDoc
prettyu (SynU f [u,v]) | Just fixity <- lookup f fixities =
  docOp2 True f fixity (prettyu u) (prettyu v)
prettyu (SynU f es) = \ prec ->
  -- (if not (null es) && prec > appPrec then parens else id) $
  maybeParens (not (null es) && prec > appPrec) $
  -- hang (text f) 2 (sep (map (flip prettyu (appPrec+1)) es))
  sep (text f : map (flip prettyu (appPrec+1)) es)

fixities :: Map String Fixity
fixities = fromList
  [ ("."  , (9,AssocRight))
  , ("&&&", (3,AssocRight))
  , ("***", (3,AssocRight))
  , ("|||", (2,AssocRight))
  , ("+++", (2,AssocRight))
  ]

renderu :: SynU -> String
renderu = renderStyle (Style PageMode 80 1) . flip prettyu 0

-- renderu = PP.render . flip prettyu 0

{--------------------------------------------------------------------
    Phantom-typed S-expression
--------------------------------------------------------------------}

newtype Syn a b = Syn SynU deriving Show

instance Newtype (Syn a b) where
  type O (Syn a b) = SynU
  pack s = Syn s
  unpack (Syn s) = s

atom :: String -> Syn a b
atom s = pack (SynU s [])

app1 :: String -> Syn a b -> Syn c d
app1 = inNew . app1u

app2 :: String -> Syn a1 b1 -> Syn a2 b2 -> Syn c d
app2 = inNew2 . app2u

pretty :: Syn a b -> PDoc
pretty = prettyu . unpack

-- instance Show (Syn a b) where show = render

render :: Syn a b -> String
render = renderu . unpack
{-# NOINLINE render #-}

-- NOINLINE here avoids the empty-case problem that was plaguing me.
-- Perhaps a strictness-based optimization forced my ccc definition.

#define INLINER(nm) {-# INLINE nm #-}
-- #define INLINER(nm)

instance Category Syn where
  id  = atom "id"
  (.) = app2 "."
  INLINER(id)
  INLINER((.))

instance ProductCat Syn where
  exl     = atom "exl"
  exr     = atom "exr"
  (&&&)   = app2 "&&&"
  (***)   = app2 "***"
  swapP   = atom "swapP"
  first   = app1 "first"
  second  = app1 "second"
  lassocP = atom "lassocP"
  rassocP = atom "rassocP"
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
  it = atom "it"
  INLINER(it)

instance CoproductCat Syn where
  inl     = atom "inl"
  inr     = atom "inr"
  (|||)   = app2 "|||"
  (+++)   = app2 "+++"
  jam     = atom "jam"
  swapS   = atom "swapS"
  left    = app1 "left"
  right   = app1 "right"
  lassocS = atom "lassocS"
  rassocS = atom "rassocS"
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
  distl = atom "distl"
  distr = atom "distr"
  INLINER(distl)
  INLINER(distr)

instance ClosedCat Syn where
  apply   = atom "apply"
  curry   = app1 "curry"
  uncurry = app1 "uncurry"
  INLINER(apply)
  INLINER(curry)
  INLINER(uncurry)

-- class Show b => HasLit b

-- instance HasLit ()
-- instance HasLit Bool
-- instance HasLit Int
-- instance HasLit Float
-- instance HasLit Double

litConst :: Show b => b -> Syn a b
litConst b = app1 "const" (atom (showPrec appPrec b))

#if 1

#define LitConst(ty) \
instance ConstCat Syn (ty) where { const = litConst ; INLINER(const) }

LitConst(())
LitConst(Bool)
LitConst(Int)
LitConst(Float)
LitConst(Double)

instance (ConstCat Syn a, ConstCat Syn b) => ConstCat Syn (a :* b) where
  const = pairConst

#else

instance Show b => ConstCat Syn b where
  const b = app1 "const" (atom (showPrec appPrec b))
  unitArrow b = app1 "unitArrow" (atom (showPrec appPrec b))
  INLINER(const)
  INLINER(unitArrow)

#endif

-- Some or all of the methods below are failing to inline

instance BoolCat Syn where
  notC = atom "notC"
  andC = atom "andC"
  orC  = atom "orC"
  xorC = atom "xorC"
  INLINER(notC)
  INLINER(andC)
  INLINER(orC)
  INLINER(xorC)

instance EqCat Syn a where
  equal    = atom "equal"
  notEqual = atom "notEqual"
  INLINER(equal)
  INLINER(notEqual)

instance OrdCat Syn a where
  lessThan = atom "lessThan"
  greaterThan = atom "greaterThan"
  lessThanOrEqual = atom "lessThanOrEqual"
  greaterThanOrEqual = atom "greaterThanOrEqual"
  INLINER(lessThan)
  INLINER(greaterThan)
  INLINER(lessThanOrEqual)
  INLINER(greaterThanOrEqual)

instance EnumCat Syn a where
  succC = atom "succC"
  predC = atom "predC"
  INLINER(succC)
  INLINER(predC)

instance NumCat Syn a where
  negateC = atom "negateC"
  addC    = atom "addC"
  subC    = atom "subC"
  mulC    = atom "mulC"
  powIC   = atom "powIC"
  INLINER(negateC)
  INLINER(addC)
  INLINER(subC)
  INLINER(mulC)
  INLINER(powIC)

instance FractionalCat Syn a where
  recipC  = atom "recipC"
  divideC = atom "divideC"
  INLINER(recipC)
  INLINER(divideC)

instance FloatingCat Syn a where
  expC = atom "expC"
  cosC = atom "cosC"
  sinC = atom "sinC"
  INLINER(expC)
  INLINER(cosC)
  INLINER(sinC)

instance FromIntegralCat Syn a b where
  fromIntegralC = atom "fromIntegralC"
  INLINER(fromIntegralC)

instance BottomCat Syn a where
  bottomC = atom "bottomC"
  INLINER(bottomC)

instance IfCat Syn a where
  ifC = atom "ifC"
  INLINER(ifC)

instance UnknownCat Syn a b where
  unknownC = atom "unknownC"
  INLINER(unknownC)

instance RepCat Syn where
  reprC = atom "reprC"
  abstC = atom "abstC"
  INLINER(reprC)
  INLINER(abstC)

{--------------------------------------------------------------------
    Pretty-printing utilities
--------------------------------------------------------------------}

type Prec   = Int
type Fixity = (Prec,Assoc)
data Assoc  = AssocLeft | AssocRight | AssocNone

type PDoc = Prec -> Doc

-- Precedence of function application.
-- Hack: use 11 instead of 10 to avoid extraneous parens when a function
-- application is the left argument of a function composition.
appPrec :: Prec
appPrec = 11 -- was 10

docOp2 :: Bool -> String -> Fixity -> Binop PDoc
docOp2 extraParens sop (p,assoc) a b q =
  maybeParens (q > p) $
  sep [a (lf p) <+> text sop, b (rf p)]
  -- hang (a (lf p) <+> text sop) 2 (b (rf p))
  -- sep [a (lf p), text sop <+> b (rf p)]
 where
   (lf,rf) = case assoc of
               AssocLeft  -> (incr, succ)
               AssocRight -> (succ, incr)
               AssocNone  -> (succ, succ)
   incr | extraParens = succ
        | otherwise   = id

showPrec :: Show a => Int -> a -> String
showPrec p a = showsPrec p a ""
