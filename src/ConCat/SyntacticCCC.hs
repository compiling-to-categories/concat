{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Syntactic CCC

module ConCat.SyntacticCCC where

import Prelude hiding (id,(.),lookup)

import Data.Map (Map,fromList,lookup)
import Control.Newtype
import Text.PrettyPrint

import ConCat.Category
import ConCat.Misc (inNew,inNew2,Binop)

{--------------------------------------------------------------------
    Untyped S-expression
--------------------------------------------------------------------}

data Sexp = Sexp String [Sexp]

atom :: String -> Sexp
atom s = Sexp s []

app1 :: String -> Sexp -> Sexp
app1 s p = Sexp s [p]

app2 :: String -> Sexp -> Sexp -> Sexp
app2 s p q = Sexp s [p,q]

pretty :: Sexp -> PDoc
pretty (Sexp f [u,v]) | Just fixity <- lookup f fixities =
  docOp2 False f fixity (pretty u) (pretty v)
pretty (Sexp f es) = \ prec ->
  (if prec > appPrec then parens else id) $
  text f <+> hsep (map (flip pretty (appPrec+1)) es)

fixities :: Map String Fixity
fixities = fromList
  [ ("."  , (9,AssocRight))
  , ("&&&", (3,AssocRight))
  , ("***", (3,AssocRight))
  , ("|||", (2,AssocRight))
  , ("+++", (2,AssocRight))
  ]

{--------------------------------------------------------------------
    Phantom-typed S-expression
--------------------------------------------------------------------}

newtype Texp a b = Texp Sexp

instance Newtype (Texp a b) where
  type O (Texp a b) = Sexp
  pack s = Texp s
  unpack (Texp s) = s

atomt :: String -> Texp a b
atomt s = pack (Sexp s [])

appt1 :: String -> Texp a b -> Texp c d
appt1 = inNew . app1

appt2 :: String -> Texp a1 b1 -> Texp a2 b2 -> Texp c d
appt2 = inNew2 . app2

prettyt :: Texp a b -> PDoc
prettyt = pretty . unpack

instance Show (Texp a b) where show = show . flip prettyt 0

instance Category Texp where
  id  = atomt "id"
  (.) = appt2 "."

instance ProductCat Texp where
  exl     = atomt "exl"
  exr     = atomt "exr"
  (&&&)   = appt2 "&&&"
  (***)   = appt2 "***"
  swapP   = atomt "swapP"
  first   = appt1 "first"
  second  = appt1 "second"
  lassocP = atomt "lassocP"
  rassocP = atomt "rassocP"

instance TerminalCat Texp where it = atomt "it"

instance CoproductCat Texp where
  inl = atomt "inl"
  inr = atomt "inr"
  (|||) = appt2 "|||"
  (+++) = appt2 "+++"
  jam = atomt "jam"
  left   = appt1 "left"
  right  = appt1 "right"
  lassocS = atomt "lassocS"
  rassocS = atomt "rassocS"
  
instance DistribCat Texp where distl = atomt "distl"

instance ClosedCat Texp where
  apply   = atomt "apply"
  curry   = appt1 "curry"
  uncurry = appt1 "uncurry"

instance Show b => ConstCat Texp b where
  const b = appt1 "const" (atomt (show b))

instance BoolCat Texp where
  notC = atomt "notC"
  andC = atomt "andC"
  orC  = atomt "orC"
  xorC = atomt "xorC"

instance EqCat Texp a where
  equal = atomt "equal"
  notEqual = atomt "notEqual"

instance OrdCat Texp a where
  lessThan = atomt "lessThan"
  greaterThan = atomt "greaterThan"
  lessThanOrEqual = atomt "lessThanOrEqual"
  greaterThanOrEqual = atomt "greaterThanOrEqual"

instance NumCat Texp a where
  negateC = atomt "negateC"
  addC    = atomt "addC"
  subC    = atomt "subC"
  mulC    = atomt "mulC"
  powIC   = atomt "powIC"

instance FractionalCat Texp a where
  recipC = atomt "recipC"
  divideC = atomt "divideC"

instance FloatingCat Texp a where
  expC = atomt "expC"
  cosC = atomt "cosC"
  sinC = atomt "sinC"

instance RepCat Texp where
  reprC = atomt "reprC"
  abstC = atomt "abstC"

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

-- TODO: Refactor showsApp & showsApp1
-- TODO: Resolve argument order

docOp2 :: Bool -> String -> Fixity -> Binop PDoc
docOp2 extraParens sop (p,assoc) a b q =
  (if q > p then parens else id) $
      a (lf p) <+> text sop <+> b (rf p)
 where
   (lf,rf) = case assoc of
               AssocLeft  -> (incr, succ)
               AssocRight -> (succ, incr)
               AssocNone  -> (succ, succ)
   incr | extraParens = succ
        | otherwise   = id
