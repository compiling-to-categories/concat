{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Syntactic CCC

module ConCat.Syntactic where

import Prelude hiding (id,(.),lookup)

import Data.Map (Map,fromList,lookup)
import Control.Newtype
import Text.PrettyPrint.HughesPJ hiding (render)

import ConCat.Category
import ConCat.Misc (inNew,inNew2,Binop)

{--------------------------------------------------------------------
    Untyped S-expression
--------------------------------------------------------------------}

data SexpU = SexpU String [SexpU] deriving Show

atomu :: String -> SexpU
atomu s = SexpU s []

app1u :: String -> SexpU -> SexpU
app1u s p = SexpU s [p]

app2u :: String -> SexpU -> SexpU -> SexpU
app2u s p q = SexpU s [p,q]

-- TODO: use the Pretty class from Text.PrettyPrint.HughesPJClass

prettyu :: SexpU -> PDoc
prettyu (SexpU f [u,v]) | Just fixity <- lookup f fixities =
  docOp2 True f fixity (prettyu u) (prettyu v)
prettyu (SexpU f es) = \ prec ->
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

renderu :: SexpU -> String
renderu = renderStyle (Style PageMode 80 1) . flip prettyu 0

-- renderu = PP.render . flip prettyu 0

{--------------------------------------------------------------------
    Phantom-typed S-expression
--------------------------------------------------------------------}

newtype Sexp a b = Sexp SexpU deriving Show

instance Newtype (Sexp a b) where
  type O (Sexp a b) = SexpU
  pack s = Sexp s
  unpack (Sexp s) = s

atom :: String -> Sexp a b
atom s = pack (SexpU s [])

app1 :: String -> Sexp a b -> Sexp c d
app1 = inNew . app1u

app2 :: String -> Sexp a1 b1 -> Sexp a2 b2 -> Sexp c d
app2 = inNew2 . app2u

pretty :: Sexp a b -> PDoc
pretty = prettyu . unpack

-- instance Show (Sexp a b) where show = render

render :: Sexp a b -> String
render = renderu . unpack

instance Category Sexp where
  id  = atom "id"
  (.) = app2 "."

instance ProductCat Sexp where
  exl     = atom "exl"
  exr     = atom "exr"
  (&&&)   = app2 "&&&"
  (***)   = app2 "***"
  swapP   = atom "swapP"
  first   = app1 "first"
  second  = app1 "second"
  lassocP = atom "lassocP"
  rassocP = atom "rassocP"

instance TerminalCat Sexp where it = atom "it"

instance CoproductCat Sexp where
  inl     = atom "inl"
  inr     = atom "inr"
  (|||)   = app2 "|||"
  (+++)   = app2 "+++"
  jam     = atom "jam"
  left    = app1 "left"
  right   = app1 "right"
  lassocS = atom "lassocS"
  rassocS = atom "rassocS"
  
instance DistribCat Sexp where distl = atom "distl"

instance ClosedCat Sexp where
  apply   = atom "apply"
  curry   = app1 "curry"
  uncurry = app1 "uncurry"

instance Show b => ConstCat Sexp b where
  const b = app1 "const" (atom (show b))

instance BoolCat Sexp where
  notC = atom "notC"
  andC = atom "andC"
  orC  = atom "orC"
  xorC = atom "xorC"

instance EqCat Sexp a where
  equal    = atom "equal"
  notEqual = atom "notEqual"

instance OrdCat Sexp a where
  lessThan = atom "lessThan"
  greaterThan = atom "greaterThan"
  lessThanOrEqual = atom "lessThanOrEqual"
  greaterThanOrEqual = atom "greaterThanOrEqual"

instance EnumCat Sexp a where
  succC = atom "succC"
  predC = atom "predC"

instance NumCat Sexp a where
  negateC = atom "negateC"
  addC    = atom "addC"
  subC    = atom "subC"
  mulC    = atom "mulC"
  powIC   = atom "powIC"

instance FractionalCat Sexp a where
  recipC  = atom "recipC"
  divideC = atom "divideC"

instance FloatingCat Sexp a where
  expC = atom "expC"
  cosC = atom "cosC"
  sinC = atom "sinC"

instance FromIntegralCat Sexp a b where
  fromIntegralC = atom "fromIntegralC"

instance BottomCat Sexp a where
  bottomC = atom "bottomC"

instance IfCat Sexp a where
  ifC = atom "ifC"

instance UnknownCat Sexp a b where
  unknownC = atom "unknownC"

instance RepCat Sexp where
  reprC = atom "reprC"
  abstC = atom "abstC"

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
