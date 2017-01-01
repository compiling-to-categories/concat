{-# LANGUAGE UndecidableInstances #-}
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

import Prelude hiding (id,(.),lookup,const,Float,Double)

import Data.Map (Map,fromList,lookup)
import Control.Newtype
import Text.PrettyPrint.HughesPJ hiding (render)
import Text.PrettyPrint.HughesPJClass hiding (render)

import ConCat.Category
import ConCat.Misc (inNew,inNew2,Unop,Binop)
-- import ConCat.Float (Float,Double)

{--------------------------------------------------------------------
    Untyped S-expression
--------------------------------------------------------------------}

data SynU = SynU PDoc [SynU]

instance Show SynU where show = showPDoc . ppretty

atomu :: Pretty a => a -> SynU
atomu a = SynU (ppretty a) []

cctext :: String -> PDoc
cctext = const . const . text

atomuStr :: String -> SynU
atomuStr s = SynU (cctext s) []

app1u :: String -> Unop SynU
app1u s p = SynU (cctext s) [p]

app2u :: String -> Binop SynU
app2u s p q = SynU (cctext s) [p,q]

instance Pretty SynU where
  pPrintPrec l p (SynU f [u,v]) | let nm = showPDoc f
                                , Just fixity <- lookup nm fixities =
    docOp2 False nm fixity (ppretty u) (ppretty v) l p
  pPrintPrec l p (SynU f es) =
    -- (if not (null es) && p > appPrec then parens else id) $
    maybeParens (not (null es) && p > appPrec) $
    -- hang (text f) 2 (sep (map (flip prettyu (appPrec+1)) es))
    sep (f l appPrec : map (pPrintPrec l (appPrec+1)) es)

fixities :: Map String Fixity
fixities = fromList
  [ ("."  , (9,AssocRight))
  , ("&&&", (3,AssocRight))
  , ("***", (3,AssocRight))
  , ("|||", (2,AssocRight))
  , ("+++", (2,AssocRight))
  ]

renderu :: SynU -> String
renderu syn = renderStyle (Style PageMode 80 1) (pPrintPrec prettyNormal 0 syn)

-- renderu = PP.render . flip prettyu 0

{--------------------------------------------------------------------
    Phantom-typed S-expression
--------------------------------------------------------------------}

newtype Syn a b = Syn SynU deriving Show

instance Newtype (Syn a b) where
  type O (Syn a b) = SynU
  pack s = Syn s
  unpack (Syn s) = s

atom :: Pretty a => a -> Syn a b
atom = pack . atomu
-- atom s = pack (atomu s)

atomStr :: String -> Syn a b
atomStr = pack . atomuStr

app1 :: String -> Syn a b -> Syn c d
app1 = inNew . app1u

app2 :: String -> Syn a1 b1 -> Syn a2 b2 -> Syn c d
app2 = inNew2 . app2u

-- pretty :: Syn a b -> PDoc
-- pretty = prettyu . unpack

-- instance Show (Syn a b) where show = render

render :: Syn a b -> String
render = renderu . unpack
{-# NOINLINE render #-}

-- NOINLINE here avoids the empty-case problem that was plaguing me.
-- Perhaps a strictness-based optimization forced my ccc definition.

#define INLINER(nm) {-# INLINE nm #-}
-- #define INLINER(nm)

instance Category Syn where
  id  = atomStr "id"
  (.) = app2 "."
  INLINER(id)
  INLINER((.))

instance ProductCat Syn where
  exl     = atomStr "exl"
  exr     = atomStr "exr"
  (&&&)   = app2 "&&&"
  (***)   = app2 "***"
  swapP   = atomStr "swapP"
  first   = app1 "first"
  second  = app1 "second"
  lassocP = atomStr "lassocP"
  rassocP = atomStr "rassocP"
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
  it = atomStr "it"
  INLINER(it)

instance CoproductCat Syn where
  inl     = atomStr "inl"
  inr     = atomStr "inr"
  (|||)   = app2 "|||"
  (+++)   = app2 "+++"
  jam     = atomStr "jam"
  swapS   = atomStr "swapS"
  left    = app1 "left"
  right   = app1 "right"
  lassocS = atomStr "lassocS"
  rassocS = atomStr "rassocS"
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
  distl = atomStr "distl"
  distr = atomStr "distr"
  INLINER(distl)
  INLINER(distr)

instance ClosedCat Syn where
  apply   = atomStr "apply"
  curry   = app1 "curry"
  uncurry = app1 "uncurry"
  INLINER(apply)
  INLINER(curry)
  INLINER(uncurry)

#if 0

litConst :: Show b => b -> Syn a b
litConst b = app1 "const" (atom (showPrec appPrec b))

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

instance Pretty b => ConstCat Syn b where
  const b = app1 "const" (atom b)
  INLINER(const)
  -- unitArrow b = app1 "unitArrow" (atom (showPrec appPrec b))
  -- INLINER(unitArrow)

#endif

-- Some or all of the methods below are failing to inline

instance BoolCat Syn where
  notC = atomStr "notC"
  andC = atomStr "andC"
  orC  = atomStr "orC"
  xorC = atomStr "xorC"
  INLINER(notC)
  INLINER(andC)
  INLINER(orC)
  INLINER(xorC)

instance EqCat Syn a where
  equal    = atomStr "equal"
  notEqual = atomStr "notEqual"
  INLINER(equal)
  INLINER(notEqual)

instance OrdCat Syn a where
  lessThan = atomStr "lessThan"
  greaterThan = atomStr "greaterThan"
  lessThanOrEqual = atomStr "lessThanOrEqual"
  greaterThanOrEqual = atomStr "greaterThanOrEqual"
  INLINER(lessThan)
  INLINER(greaterThan)
  INLINER(lessThanOrEqual)
  INLINER(greaterThanOrEqual)

instance EnumCat Syn a where
  succC = atomStr "succC"
  predC = atomStr "predC"
  INLINER(succC)
  INLINER(predC)

instance NumCat Syn a where
  negateC = atomStr "negateC"
  addC    = atomStr "addC"
  subC    = atomStr "subC"
  mulC    = atomStr "mulC"
  powIC   = atomStr "powIC"
  INLINER(negateC)
  INLINER(addC)
  INLINER(subC)
  INLINER(mulC)
  INLINER(powIC)

instance FractionalCat Syn a where
  recipC  = atomStr "recipC"
  divideC = atomStr "divideC"
  INLINER(recipC)
  INLINER(divideC)

instance FloatingCat Syn a where
  expC = atomStr "expC"
  cosC = atomStr "cosC"
  sinC = atomStr "sinC"
  INLINER(expC)
  INLINER(cosC)
  INLINER(sinC)

instance FromIntegralCat Syn a b where
  fromIntegralC = atomStr "fromIntegralC"
  INLINER(fromIntegralC)

instance BottomCat Syn a where
  bottomC = atomStr "bottomC"
  INLINER(bottomC)

instance IfCat Syn a where
  ifC = atomStr "ifC"
  INLINER(ifC)

instance UnknownCat Syn a b where
  unknownC = atomStr "unknownC"
  INLINER(unknownC)

instance RepCat Syn a where
  reprC = atomStr "reprC"
  abstC = atomStr "abstC"
  INLINER(reprC)
  INLINER(abstC)

instance CoerceCat Syn a b where
  coerceC = atomStr "coerceC"
  INLINER(coerceC)

{--------------------------------------------------------------------
    Pretty-printing utilities
--------------------------------------------------------------------}

type Prec   = Rational
type Fixity = (Prec,Assoc)
data Assoc  = AssocLeft | AssocRight | AssocNone

type PDoc = PrettyLevel -> Prec -> Doc

ppretty :: Pretty a => a -> PDoc
ppretty a l p = pPrintPrec l p a

showPDoc :: PDoc -> String
showPDoc d = show (d prettyNormal 0)

-- Precedence of function application.
-- Hack: use 11 instead of 10 to avoid extraneous parens when a function
-- application is the left argument of a function composition.
appPrec :: Prec
appPrec = 11 -- was 10

docOp2 :: Bool -> String -> Fixity -> Binop PDoc
docOp2 extraParens sop (p,assoc) a b l q =
  maybeParens (q > p) $
  sep [a l (lf p) <+> text sop, b l (rf p)]
  -- hang (a l (lf p) <+> text sop) 2 (b l (l rf p))
  -- sep [a l (lf p), text sop <+> b l (rf p)]
 where
   (lf,rf) = case assoc of
               AssocLeft  -> (incr, succ)
               AssocRight -> (succ, incr)
               AssocNone  -> (succ, succ)
   incr | extraParens = succ
        | otherwise   = id

showPrec :: Show a => Int -> a -> String
showPrec p a = showsPrec p a ""
