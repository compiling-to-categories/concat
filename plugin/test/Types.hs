{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}

module Types where

import qualified ConCat.Category as CC
import           Test.Hspec
import Unsafe.Coerce (unsafeCoerce)


data Chillin a b where
  CId   :: Chillin a b
  CComp :: Chillin b c -> Chillin a b -> Chillin a c
  CFloat :: Float -> Chillin a Float
  CExl :: Chillin (a, b) a
  CExr :: Chillin (a, b) b
  CPAnd :: Chillin a b -> Chillin a c -> Chillin a (b, c)
  CCurry :: Chillin (a, b) c -> Chillin a (b -> c)
  CApply :: Chillin (a -> b, a) b
  CMul :: Chillin (a, a) a
  CAdd :: Chillin (a, a) a
  CPow :: Chillin (a, Int) a
  CNeg :: Chillin a a

deriving instance Show (Chillin a b)

instance Eq (Chillin a b) where
  CId == CId = True
  CComp a b == CComp c d =
    and [ unsafeCoerce a == c
        , unsafeCoerce b == d
        ]
  CFloat a == CFloat b = a == b
  _ == _ = False
  {-# INLINE (==) #-}

instance CC.Category Chillin where
  id = CId
  (.) = CComp
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance CC.ProductCat Chillin where
  exl = CExl
  exr = CExr
  (&&&) = CPAnd
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

instance CC.ClosedCat Chillin where
  curry = CCurry
  apply = CApply
  {-# INLINE curry #-}
  {-# INLINE apply #-}

instance Num a => CC.NumCat Chillin a where
  addC = CAdd
  mulC = CMul
  negateC = CNeg
  powIC = CPow
  {-# INLINE addC #-}
  {-# INLINE mulC #-}
  {-# INLINE negateC #-}
  {-# INLINE powIC #-}

