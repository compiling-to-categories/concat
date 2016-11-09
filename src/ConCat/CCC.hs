{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, KindSignatures, CPP #-}
{-# LANGUAGE PatternGuards, ViewPatterns, ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}   -- for Int1 hack
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.CCC
-- Copyright   :  (c) 2013 Tabula Inc and 2016 Conal Elliott
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- GADT of CCC combinators
----------------------------------------------------------------------

-- -- Whether to introduce defined operations like (***) during show
-- #define Sugared

-- -- Whether to simplify during construction
-- #define Simplify

module ConCat.CCC
  ( (:->)(..)
  -- , Convert
  ) where

import Prelude hiding (id,(.),curry,uncurry)
-- import Data.Typeable (Typeable)
-- import Data.Coerce

#ifdef Simplify
-- import Data.IsTy
import Data.Type.Equality
#endif

-- import TypeUnary.Vec (Vec(..))

import ConCat.Misc (Unop,Evalable(..),(:*),(:+),(:=>),Eq'(..),(==?))
import ConCat.ShowUtils (showsApp1,showsOp2',Assoc(..))
-- import ConCat.Ty
-- import ConCat.Prim (Prim(..),Lit(..),primArrow) -- ,cond,ifThenElse

-- import TypeEncode.Encode (EncodeCat(..))

import ConCat.Category
-- import ConCat.Circuit ((:>),GenBuses)

infix  0 :->

infixr 3 :&&&
infixr 2 :|||

-- | CCC combinator expressions. Although we use standard Haskell unit,
-- cartesian product, sums, and function types here, the intended interpretation
-- is as the categorical counterparts (terminal object, categorical products,
-- coproducts, and exponentials).
data (:->) :: * -> * -> * where
  Id      :: a :-> a
  (:.)    :: (b :-> c) -> (a :-> b) -> (a :-> c)
  -- Products
  Exl     :: a :* b :-> a
  Exr     :: a :* b :-> b
  (:&&&)  :: (a :-> b) -> (a :-> c) -> (a :-> b :* c)
  It      :: a :-> ()
  -- Coproducts
  Inl     :: a :-> a :+ b
  Inr     :: b :-> a :+ b
  (:|||)  :: (b :-> a) -> (c :-> a) -> (b :+ c :-> a)
  DistL   :: a :* (b :+ c) :-> a :* b :+ a :* c
  -- Exponentials
  Apply   :: (a :=> b) :* a :-> b
  Curry   :: (a :* b :-> c) -> (a :-> (b :=> c))
  Uncurry :: (a :-> (b :=> c)) -> (a :* b :-> c)
--   -- Type-safe coercion
--   Coerce  :: (Typeable a, Typeable b, Coercible a b) => a :-> b
--   -- Representation change
--   Repr    :: a :-> Rep a
--   Abst    :: Rep a :-> a

--   -- Primitives
--   Prim    :: Prim (a :=> b) -> (a :-> b)
--   Lit     :: Lit b -> (a :-> b)

-- TODO: Maybe specialize a to () in the type of Lit

-- TODO: Try to make instances for the Category subclasses, so we don't need
-- separate terminology. Then eliminate dup, jam, etc.

instance Eq' (a :-> b) (c :-> d) where
  Id         === Id           = True
  (g :. f)   === (g' :. f')   = g === g' && f === f'
  Exl        === Exl          = True
  Exr        === Exr          = True
  (f :&&& g) === (f' :&&& g') = f === f' && g === g'
  Inl        === Inl          = True
  Inr        === Inr          = True
  (f :||| g) === (f' :||| g') = f === f' && g === g'
  DistL      === DistL        = True
  Apply      === Apply        = True
  Curry h    === Curry h'     = h === h'
  Uncurry k  === Uncurry k'   = k === k'
--   Prim p     === Prim p'      = p === p'
--   Lit l      === Lit l'       = l === l'
  _          === _            = False

instance Eq (a :-> b) where (==) = (===)


-- WARNING: take care with the (==) definition above. When we add constructors
-- to the GADT, we won't get a non-exhaustive cases warning, since the last case
-- is catch-all.

-- TODO: The type constraints prevent (:->) from being a category etc without
-- some change to those classes, e.g., with instance-specific constraints via
-- ConstraintKinds.

-- Maybe parametrize this GADT by a constraint. Sadly, I'd lose the pretty infix
-- syntax ("a :-> b").

-- Homomorphic evaluation
#if 1

distlF :: a :* (b :+ c) -> a :* b :+ a :* c
distlF (a, Left  b) = Left  (a,b)
distlF (a, Right c) = Right (a,c)

-- instance Evalable (a :-> b) where
--   type ValT (a :-> b) = a :=> b
--   eval Id          = id
--   eval (g :. f)    = eval g . eval f
--   eval Exl         = fst
--   eval Exr         = snd
--   eval (f :&&& g)  = eval f &&& eval g
--   eval It          = it
--   eval Inl         = Left
--   eval Inr         = Right
--   eval (f :||| g)  = eval f ||| eval g
--   eval DistL       = distlF
--   eval Apply       = uncurry ($)
--   eval (Curry   h) = curry   (eval h)
--   eval (Uncurry f) = uncurry (eval f)
-- --   eval Coerce      = coerce
--   eval (Prim p)    = eval p
--   eval (Lit l)     = const (eval l)
-- #else
-- instance Evalable (a :-> b) where
--   type ValT (a :-> b) = a -> b
--   eval = convertC

#endif


{--------------------------------------------------------------------
    Smart constructors
--------------------------------------------------------------------}

-- prim :: Prim (a -> b) -> (a :-> b)
-- prim ExlP = Exl
-- prim ExrP = Exr
-- prim InlP = Inl
-- prim InrP = Inr
-- prim p    = Prim p

instance Category (:->) where
  id  = Id
  -- | Optimizing morphism composition
# ifdef Simplify
  Id         . f                   = f
  g          . Id                  = g
  (h :. g)   . f                   = h . (g . f)
  Exl        . (f :&&& _)          = f
  Exr        . (_ :&&& g)          = g
  It          . _                  = it
  (f :||| _) . Inl                 = f
  (_ :||| g) . Inr                 = g
  -- Important but occasionally leads to nontermination.
  -- See https://github.com/conal/lambda-ccc/issues/14
--   Apply      . (decompL -> g :. f) = composeApply g . f
  -- Even the following simpler version trips nontermination.
--   Apply     . (decompL -> g :. f)  = (Apply :. g) . f
--   Curry (decompR -> f :. Exr) . _  = curry (f . exr)  -- see below
# endif
  g          . f                   = g :. f


-- To prove:
-- 
--   curry (f . exr) . g == curry (f . exr)

#ifdef Simplify

-- | @'composeApply' h == 'apply' . h@
composeApply :: (z :-> (a :=> b) :* a) -> (z :-> b)
-- apply . (curry h . f &&& g) == h . (f &&& g)
composeApply ((decompL -> (Curry h :. f)) :&&& g) = h . (f &&& g)
composeApply (h@Prim{} :. f    :&&& g) = uncurry h . (f  &&& g)
composeApply (h@Prim{}         :&&& g) = uncurry h . (Id &&& g)
-- apply . (curry (g . exr) &&& f) == g . f
composeApply (Curry (decompR -> g :. Exr) :&&& f) = g . f
-- apply . first f == uncurry f  -- see proof below
composeApply (f :. Exl :&&& Exr) = uncurry f
composeApply h = Apply :. h

#endif

{-
  apply . first f
== \ p -> apply (first f p)
== \ (a,b) -> apply (first f (a,b))
== \ (a,b) -> apply (f a, b)
== \ (a,b) -> f a b
== uncurry f
-}

-- Note: the ConstU{} specialization is unnecessary for validity but I suspect
-- useful for introducing just the uncurryings we want. TODO: verify.
--
-- Note: the second Uncurry specializes the first one, but is needed for
-- syntactic matching.

instance ProductCat (:->) where
  type Prod (:->) = (:*)
  exl = Exl
  exr = Exr
# ifdef Simplify
  -- Experimental: const a &&& const b == const (a,b)
  -- Prim (ConstP (LitP a)) &&& Prim (ConstP (LitP b)) = Prim (ConstP (LitP (a,b)))
  Exl &&& Exr = Id
  -- f . r &&& g . r == (f &&& g) . r
  (decompR -> f :. r) &&& (decompR -> g :. r') | Just Refl <- r ==? r'
                                               = (f &&& g) . r
# endif
  f &&& g = f :&&& g

-- TODO: Can I use other than (:*) etc by tweaking the (:->) constructor types?

instance TerminalCat (:->) where
  type Unit (:->) = ()
  it = It

instance CoproductCat (:->) where
  type Coprod (:->) = (:+)
  inl   = Inl
  inr   = Inr
  (|||) = (:|||)                            -- no rewrites?

instance DistribCat (:->) where
  distl = DistL

instance ClosedCat (:->) where
  type Exp (:->) = (->)
  apply = Apply
# ifdef Simplify
  curry (Uncurry h) = h
  -- curry (apply . (f . exl &&& exr)) == f  -- Proof below
  -- curry (Apply :. (f :. Exl :&&& Exr)) = f
# endif
  curry h = Curry h
# ifdef Simplify
  uncurry (Curry f)    = f
  uncurry (Prim PairP) = Id
# endif
  uncurry x = Uncurry x

-- curry/apply proof:
-- 
--   curry (apply . (f . exl &&& exr))
-- == curry (apply . (f . exl &&& id . exr))
-- == curry (apply . (f *** id))
-- == curry (apply . first f)
-- == curry (\ (a,b) -> apply (first f (a,b)))
-- == curry (\ (a,b) -> apply (f a,b))
-- == curry (\ (a,b) -> f a b)
-- == f

-- I commented out this rule. I don't think it'll ever fire, considering
-- composeApply.

-- instance CoerceCat (:->) where
--   coerceC = Coerce

-- instance RepCat (:->) where
--   reprC = prim ReprP
--   abstC = prim AbstP

-- instance BottomCat (:->) where
--   type BottomKon (:->) a = GenBuses a
--   bottomC = prim BottomC

{--------------------------------------------------------------------
    Factoring (decomposition)
--------------------------------------------------------------------}

#if defined Simplify

-- | Decompose into @g . f@, where @g@ is as small as possible, but not 'Id'.
-- Pattern matching against @_ :. _@ determines whether decomposition succeeded.
decompL :: Unop (a :-> c)
decompL Id                         = Id
decompL ((decompL -> h :. g) :. f) = h :. (g . f)
decompL comp@(_ :. _)              = comp
decompL f                          = f :. Id

#endif

#if defined Simplify || defined Sugared

-- | Decompose into @g . f@, where @f@ is as small as possible, but not 'Id'.
-- Pattern matching against @_ :. _@ determines whether decomposition succeeded.
decompR :: Unop (a :-> c)
decompR Id                         = Id
decompR (h :. (decompR -> g :. f)) = (h . g) :. f
decompR comp@(_ :. _)              = comp
decompR f                          = Id :. f

#endif

{--------------------------------------------------------------------
    Show
--------------------------------------------------------------------}

instance Show (a :-> b) where
#ifdef Sugared
  showsPrec _ (Id  :&&& Id )   = showString "dup"
  showsPrec _ (Exr :&&& Exl)   = showString "swapP"
  showsPrec p ((decompR -> f :. Exl) :&&& (decompR -> g :. Exr))
    | Id <- g                  = showsApp1 "first"  p f
    | Id <- f                  = showsApp1 "second" p g
    | f === g                  = showsApp1 "twiceP" p f
    | otherwise                = showsOp2'  "***" (3,AssocRight) p f g
  showsPrec _ (Id  :||| Id )   = showString "jam"
  showsPrec _ (Inr :||| Inl)   = showString "swapC"
  showsPrec p ((decompR -> f :. Inl) :&&& (decompR -> g :. Inr))
    | Id <- g                  = showsApp1 "left"  p f
    | Id <- f                  = showsApp1 "right" p g
    | f === g                  = showsApp1 "twiceC" p f
    | otherwise                = showsOp2'  "+++" (2,AssocRight) p f g
#endif
  showsPrec _ Id          = showString "id"
  showsPrec p (g :. f)    = showsOp2'  "."  (9,AssocRight) p g f
  showsPrec _ Exl         = showString "exl"
  showsPrec _ Exr         = showString "exr"
  showsPrec p (f :&&& g)  = showsOp2'  "&&&" (3,AssocRight) p f g
  showsPrec _ It          = showString "it"
  showsPrec _ Inl         = showString "inl"
  showsPrec _ Inr         = showString "inr"
  showsPrec p (f :||| g)  = showsOp2'  "|||" (2,AssocRight) p f g
  showsPrec _ DistL       = showString "distl"
  showsPrec _ Apply       = showString "apply"
  showsPrec p (Curry   f) = showsApp1  "curry"   p f
  showsPrec p (Uncurry h) = showsApp1  "uncurry" p h
--   showsPrec p (Prim x)    = showsPrec p x
--   showsPrec p (Lit l)     = showsApp1 "const" p l

-- -- | Category with boolean operations.
-- class ProductCat k => BoolCat k where
--   not :: Bool `k` Bool
--   and, or, xor :: (Bool :* Bool) `k` Bool

-- primUnc :: Prim (a :=> b :=> c) -> (a :* b :-> c)
-- primUnc = uncurry . prim

-- instance BoolCat (:->) where
--   notC = prim NotP
--   xorC = uncurry (prim XorP)
--   andC = uncurry (prim AndP)
--   orC  = uncurry (prim OrP)

-- etc.

#if 0
instance MuxCat (:->) where
  muxB = prim CondBP
  muxI = prim CondIP
#else

-- instance IfCat (:->) a where
--   ifC = prim IfP

--     No instance for (IfCat (ConCat.Circuit.:>) a)

#endif

-- instance NumCat (:->) Int where
--   add = primUnc AddP
--   sub = primUnc SubP
--   mul = primUnc MulP

-- TODO: reconcile curried vs uncurried, eliminating the conversions here.

{--------------------------------------------------------------------
    Experiment: convert to other CCC
--------------------------------------------------------------------}

type family C (k :: u -> u -> *) (a :: *) :: u

type instance C k (a :* b) = Prod k (C k a) (C k b)

convertC :: -- ( BiCCCC k Lit, BoolCat k, NumCat k Int)
            -- (k ~ (:>))
            (ClosedCat k)
         -- => Oks k '[C k a, C k b]
         => (Ok k (C k a), Ok k (C k b))
         => (a :-> b) -> (C k a `k` C k b)
convertC = undefined

-- convertC Id           = id
-- convertC (g :. f)     = convertC g . convertC f

-- convertC Exl          = exl
-- convertC Exr          = exr
-- convertC (f :&&& g)   = convertC f &&& convertC g
-- convertC It           = it
-- convertC Inl          = inl
-- convertC Inr          = inr
-- convertC (f :||| g)   = convertC f ||| convertC g
-- convertC DistL        = distl
-- convertC Apply        = apply
-- convertC (Curry   h)  = curry   (convertC h)
-- convertC (Uncurry f)  = uncurry (convertC f)

-- convertC (Prim p)     = primArrow p
-- convertC (Lit l)      = unitArrow l . it

-- instance HasUnitArrow (:->) Lit where unitArrow = Lit


-- TODO: define OkCs via AllC, and use in convertC.


data Convert (k :: u -> u -> *)

instance ClosedCat k => FunctorC (Convert k) (:->) k where
  type Convert k :% a = C k a
  type OkF (Convert k) a b = (Ok k (C k a), Ok k (C k b))
  fmapC = convertC

--   fmapC Id = id
--   fmapC (g :. f) = fmapC g . fmapC f
