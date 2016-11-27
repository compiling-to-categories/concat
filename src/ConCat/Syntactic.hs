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

data SynU = SynU String [SynU] deriving Show

atomu :: String -> SynU
atomu s = SynU s []

app1u :: String -> SynU -> SynU
app1u s p = SynU s [p]

app2u :: String -> SynU -> SynU -> SynU
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

instance Category Syn where
  id  = atom "id"
  (.) = app2 "."

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

instance TerminalCat Syn where it = atom "it"

instance CoproductCat Syn where
  inl     = atom "inl"
  inr     = atom "inr"
  (|||)   = app2 "|||"
  (+++)   = app2 "+++"
  jam     = atom "jam"
  left    = app1 "left"
  right   = app1 "right"
  lassocS = atom "lassocS"
  rassocS = atom "rassocS"
  
instance DistribCat Syn where distl = atom "distl"

instance ClosedCat Syn where
  apply   = atom "apply"
  curry   = app1 "curry"
  uncurry = app1 "uncurry"

instance Show b => ConstCat Syn b where
  const b = app1 "const" (atom (show b))

instance BoolCat Syn where
  notC = atom "notC"
  andC = atom "andC"
  orC  = atom "orC"
  xorC = atom "xorC"

instance EqCat Syn a where
  equal    = atom "equal"
  notEqual = atom "notEqual"

instance OrdCat Syn a where
  lessThan = atom "lessThan"
  greaterThan = atom "greaterThan"
  lessThanOrEqual = atom "lessThanOrEqual"
  greaterThanOrEqual = atom "greaterThanOrEqual"

instance EnumCat Syn a where
  succC = atom "succC"
  predC = atom "predC"

instance NumCat Syn a where
  negateC = atom "negateC"
  addC    = atom "addC"
  subC    = atom "subC"
  mulC    = atom "mulC"
  powIC   = atom "powIC"

instance FractionalCat Syn a where
  recipC  = atom "recipC"
  divideC = atom "divideC"

instance FloatingCat Syn a where
  expC = atom "expC"
  cosC = atom "cosC"
  sinC = atom "sinC"

instance FromIntegralCat Syn a b where
  fromIntegralC = atom "fromIntegralC"

instance BottomCat Syn a where
  bottomC = atom "bottomC"

instance IfCat Syn a where
  ifC = atom "ifC"

instance UnknownCat Syn a b where
  unknownC = atom "unknownC"

instance RepCat Syn where
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
