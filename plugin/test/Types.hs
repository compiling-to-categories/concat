{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Types where

import qualified ConCat.Category as CC
import           Data.Typeable
import           Unsafe.Coerce (unsafeCoerce)


----------------------------------------------------------------------------
-- | The free category construction over all of the relevant concat classes.
data FreeSyn a b where
  CId    :: FreeSyn a a
  CComp  :: FreeSyn b c -> FreeSyn a b -> FreeSyn a c
  CTerm  :: FreeSyn a ()
  CExl   :: FreeSyn (a, b) a
  CExr   :: FreeSyn (a, b) b
  CPAnd  :: FreeSyn a b -> FreeSyn a c -> FreeSyn a (b, c)
  CCurry :: FreeSyn (a, b) c -> FreeSyn a (b -> c)
  CApply :: FreeSyn (a -> b, a) b
  CMul   :: FreeSyn (a, a) a
  CAdd   :: FreeSyn (a, a) a
  CPow   :: FreeSyn (a, Int) a
  CNeg   :: FreeSyn a a
  CInl   :: FreeSyn a (Either a b)
  CInr   :: FreeSyn b (Either a b)
  CCOr   :: FreeSyn a c -> FreeSyn b c -> FreeSyn (Either a b) c
  CConst :: (Show b, Eq b, Typeable b) => b -> FreeSyn a b
  CDistl :: FreeSyn (a, Either u v) (Either (a, u) (a, v))



instance Show (FreeSyn a b) where
  show CId         = "id"
  show (CComp a b) = "(comp " ++ show a ++ " " ++ show b ++ ")"
  show CTerm       = "unit"
  show CExl        = "exl"
  show CExr        = "exr"
  show (CPAnd a b) = "(and " ++ show a ++ " " ++ show b ++ ")"
  show (CCurry a)  = "(curry " ++ show a ++ ")"
  show CApply      = "app"
  show CMul        = "mul"
  show CAdd        = "add"
  show CPow        = "pow"
  show CNeg        = "neg"
  show CInl        = "inl"
  show CInr        = "inr"
  show (CCOr a b)  = "(or " ++ show a ++ " " ++ show b ++ ")"
  show (CConst a)  = "(const " ++ show a ++ ")"
  show CDistl      = "distl"


instance Eq (FreeSyn a b) where
  CId == CId = True
  CComp a b == CComp c d =
    -- safe enough for test code, unless we do a bad coerce of 'CConst' in
    -- which case bad things will happen
    and [ unsafeCoerce a == c
        , unsafeCoerce b == d
        ]
  CTerm     == CTerm = True
  CExl      == CExl = True
  CExr      == CExr = True
  CPAnd a b == CPAnd c d = a == c && b == d
  CCurry a  == CCurry b = a == b
  CMul      == CMul = True
  CAdd      == CAdd = True
  CPow      == CPow = True
  CNeg      == CNeg = True
  CInl      == CInl = True
  CInr      == CInr = True
  CCOr a b  == CCOr c d = a == c && b == d
  CConst a  == CConst b = cast a == Just b
  CDistl    == CDistl = True
  _         == _ = False


instance CC.Category FreeSyn where
  id = CId
  (.) = CComp
  {-# INLINE id #-}
  {-# INLINE (.) #-}


instance CC.ProductCat FreeSyn where
  exl = CExl
  exr = CExr
  (&&&) = CPAnd
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}


instance CC.ClosedCat FreeSyn where
  curry = CCurry
  apply = CApply
  {-# INLINE curry #-}
  {-# INLINE apply #-}


instance Num a => CC.NumCat FreeSyn a where
  addC = CAdd
  mulC = CMul
  negateC = CNeg
  powIC = CPow
  {-# INLINE addC #-}
  {-# INLINE mulC #-}
  {-# INLINE negateC #-}
  {-# INLINE powIC #-}


instance CC.CoproductCat FreeSyn where
  inl = CInl
  inr = CInr
  (|||) = CCOr
  {-# INLINE inl #-}
  {-# INLINE inr #-}
  {-# INLINE (|||) #-}


instance CC.TerminalCat FreeSyn where
  it = CTerm
  {-# INLINE it #-}


instance (Show a, Eq a, Typeable a) => CC.ConstCat FreeSyn a where
  const = CConst
  {-# INLINE const #-}

instance CC.DistribCat FreeSyn where
  distl = CDistl
  {-# INLINE distl #-}
