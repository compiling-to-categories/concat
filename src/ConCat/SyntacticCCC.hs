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

atomu :: String -> Sexp
atomu s = Sexp s []

app1u :: String -> Sexp -> Sexp
app1u s p = Sexp s [p]

app2u :: String -> Sexp -> Sexp -> Sexp
app2u s p q = Sexp s [p,q]

prettyu :: Sexp -> PDoc
prettyu (Sexp f [u,v]) | Just fixity <- lookup f fixities =
  docOp2 False f fixity (prettyu u) (prettyu v)
prettyu (Sexp f es) = \ prec ->
  (if prec > appPrec then parens else id) $
  text f <+> hsep (map (flip prettyu (appPrec+1)) es)

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

atom :: String -> Texp a b
atom s = pack (Sexp s [])

app1 :: String -> Texp a b -> Texp c d
app1 = inNew . app1u

app2 :: String -> Texp a1 b1 -> Texp a2 b2 -> Texp c d
app2 = inNew2 . app2u

pretty :: Texp a b -> PDoc
pretty = prettyu . unpack

instance Show (Texp a b) where show = show . flip pretty 0

instance Category Texp where
  id  = atom "id"
  (.) = app2 "."

instance ProductCat Texp where
  exl     = atom "exl"
  exr     = atom "exr"
  (&&&)   = app2 "&&&"
  (***)   = app2 "***"
  swapP   = atom "swapP"
  first   = app1 "first"
  second  = app1 "second"
  lassocP = atom "lassocP"
  rassocP = atom "rassocP"

instance TerminalCat Texp where it = atom "it"

instance CoproductCat Texp where
  inl = atom "inl"
  inr = atom "inr"
  (|||) = app2 "|||"
  (+++) = app2 "+++"
  jam = atom "jam"
  left   = app1 "left"
  right  = app1 "right"
  lassocS = atom "lassocS"
  rassocS = atom "rassocS"
  
instance DistribCat Texp where distl = atom "distl"

instance ClosedCat Texp where
  apply   = atom "apply"
  curry   = app1 "curry"
  uncurry = app1 "uncurry"

instance Show b => ConstCat Texp b where
  const b = app1 "const" (atom (show b))

instance BoolCat Texp where
  notC = atom "notC"
  andC = atom "andC"
  orC  = atom "orC"
  xorC = atom "xorC"

instance EqCat Texp a where
  equal = atom "equal"
  notEqual = atom "notEqual"

instance OrdCat Texp a where
  lessThan = atom "lessThan"
  greaterThan = atom "greaterThan"
  lessThanOrEqual = atom "lessThanOrEqual"
  greaterThanOrEqual = atom "greaterThanOrEqual"

instance NumCat Texp a where
  negateC = atom "negateC"
  addC    = atom "addC"
  subC    = atom "subC"
  mulC    = atom "mulC"
  powIC   = atom "powIC"

instance FractionalCat Texp a where
  recipC = atom "recipC"
  divideC = atom "divideC"

instance FloatingCat Texp a where
  expC = atom "expC"
  cosC = atom "cosC"
  sinC = atom "sinC"

instance RepCat Texp where
  reprC = atom "reprC"
  abstC = atom "abstC"

{--------------------------------------------------------------------
    Prettyu-printing utilities
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
