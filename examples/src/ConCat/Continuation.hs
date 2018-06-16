{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Continuation-passing category

module ConCat.Continuation where

import Prelude hiding (id,(.),uncurry)

import Data.Constraint (Dict(..),(:-)(..))
import Data.Key (Zip)

import ConCat.Misc ((:*))
import ConCat.Rep
import qualified ConCat.Category
import ConCat.AltCat
import ConCat.Additive (Additive)

newtype Cont k r a b = Cont ((b `k` r) -> (a `k` r))

-- Could (->) here be another category? I think so.

instance HasRep (Cont k r a b) where
  type Rep (Cont k r a b) = (b `k` r) -> (a `k` r)
  abst f = Cont f
  repr (Cont f) = f

cont :: (Category k, Ok3 k r a b) => (a `k` b) -> Cont k r a b
cont f = abst (. f)

instance Category (Cont k r) where
  type Ok (Cont k r) = Ok k
  id = Cont id
  (.) = inAbst2 (flip (.))

instance (ProductCat k, TerminalCat k, CoterminalCat k, CoproductPCat k, OkAdd k, Ok k r)
      => MonoidalPCat (Cont k r) where
  (***) :: forall a b c d. Ok4 k a b c d
        => Cont k r a c -> Cont k r b d -> Cont k r (Prod k a b) (Prod k c d)
  -- (***) = undefined
  Cont f *** Cont g = Cont (joinP . (f *** g) . unjoinP) 
    <+ okAdd @k @c
    <+ okAdd @k @d
    <+ okAdd @k @r

-- TODO: Give non-default definitions for lassocP and rassocP, and relax
-- ProductCat k back to MonoidalPCat and drop TerminalCat k and CoterminalCat if
-- possible.

instance (ProductCat k, TerminalCat k, CoproductPCat k, CoterminalCat k, OkAdd k, Ok k r)
      => BraidedPCat (Cont k r)
-- TODO: non-default swapP with simpler preconditions.

instance (ProductCat k, CoproductPCat k, AbelianCat k, OkAdd k, Ok k r)
      => ProductCat (Cont k r) where
  exl :: forall a b. Ok2 k a b => Cont k r (a :* b) a
  exl = Cont (|||| zeroC) <+ okAdd @k @r
  -- exl = cont exl <+ okProd @k @a @b
  exr :: forall a b. Ok2 k a b => Cont k r (a :* b) b
  -- exr = cont exr <+ okProd @k @a @b
  exr = Cont (zeroC ||||) <+ okAdd @k @r
  dup :: forall a. Ok k a => Cont k r a (a :* a)
  dup = Cont (uncurry plusC . unjoinP)
    <+ okAdd @k @a
    <+ okAdd @k @r
  -- (&&&) :: forall a c d. Ok3 k a c d
  --       => Cont k r a c -> Cont k r a d -> Cont k r a (Prod k c d)
  -- (&&&) = undefined
  -- (&&&) = inAbst2 (\ f g -> (f |||| g) . unjoinP) 
  -- (&&&) = inAbst2 (\ f g -> uncurry plusC . (f *** g) . unjoinP) 
  --   <+ okAdd @k @c
  --   <+ okAdd @k @d
  --   <+ okAdd @k @r

-- h            :: a `k` r
--        zeroC :: b `k` r
-- h |||| zeroC :: (a :* b) `k` r

-- Could not deduce (CoproductPCat (->))
--   arising from a use of ‘||||’

-- The constraint ‘Ok k r’ is no smaller than the instance head
-- (Use UndecidableInstances to permit this)

--            f         :: (c `k` r) -> (a `k` r)
--                   g  :: (d `k` r) -> (a `k` r)
--            f |||| g  :: (c `k` r) :* (d `k` r) -> (a `k` r)
-- (f |||| g) . unjoinP :: ((c :* d) `k` r) -> (a `k` r)

-- instance (CoproductPCat k, Ok k r) => CoproductPCat (Cont k r) where
--   inlP :: forall a b. Ok2 k a b => Cont k r a (a :* b)
--   inlP = cont inlP <+ okProd @k @a @b
--   inrP :: forall a b. Ok2 k a b => Cont k r b (a :* b)
--   inrP = cont inrP <+ okProd @k @a @b
--   (||||) = inAbst2 (\ f g -> uncurry (||||) . (f &&& g))


--            f       :: (c `k` r) -> (a `k` r)
--                  g :: (c `k` r) -> (b `k` r)
--            f &&& g :: (c `k` r) -> (a `k` r) :* (b `k` r)
-- uncurry (||||) . (f &&& g) :: (c `k` r) -> ((a :* b) `k` r)

-- TODO: Fix the ProductCat and CoproductPCat instances to match the paper.

instance UnitCat (Cont k r)

-- class (Category k, OkIxProd k h) => IxMonoidalPCat k h where
--   crossF :: forall a b. Ok2 k a b => h (a `k` b) -> (h a `k` h b)

instance (OkIxProd k h, Additive1 h, OkAdd k) => OkIxProd (Cont k r) h where
  okIxProd :: forall a. Ok' (Cont k r) a |- Ok' (Cont k r) (h a)
  okIxProd = Entail (Sub (Dict <+ okIxProd @k @h @a <+ additive1 @h @a <+ okAdd @k @a))

instance (Zip h, IxCoproductPCat k h, Additive1 h, OkAdd k, Ok k r)
      => IxMonoidalPCat (Cont k r) h where
  crossF :: forall a b. Ok2 k a b => h (Cont k r a b) -> Cont k r (h a) (h b)
  crossF fs = Cont (joinPF . crossF (repr <$> fs) . ConCat.AltCat.unjoinPF) 

-- instance ({- Zip h, IxCoproductPCat k h, Additive1 h, OkAdd k, Ok k r-})
--       => IxProductCat (Cont k r) h where


instance (IxCoproductPCat k h, Zip h, Additive1 h, OkAdd k, Ok k r)
      => IxProductCat (Cont k r) h where
  exF    :: forall a. Ok (Cont k r) a => h (Cont k r (h a) a)
  replF  :: forall a. Ok (Cont k r) a => Cont k r a (h a)
  exF = undefined
        -- ((Cont . joinPF) .) <$> inPF
  replF = undefined

#if 0

inPF :: h (a `k` h a)

fmap (joinPF .) inPF :: 


need :: h ((a `k` r) -> (h a `k` r))

f :: a `k` h a

f' ::  (a `k` r) -> (h a `k` r)

joinPF :: (IxCoproductPCat k h, Ok2 k a b) => h (b `k` a) -> (h b `k` a)


#endif

-- joinPF :: forall a b . (IxProductCat k, Ok2 k a b) => h (b `k` a) -> (h b `k` a)
-- unjoinPF :: forall a b . (IxProductCat k, Ok2 k a b) => (h b `k` a) -> h (b `k` a)



-- instance ProductCat k => ProductCat (ContC k r) where
--   exl  = Cont (join . inl)
--   exr  = Cont (join . inr)
--   dup  = Cont (jamP . unjoin)

#if 0

exl :: Cont k r (a :* b) a
Cont (join . inl) :: Cont k r (a :* b) a
join . inl :: (a `k` r) -> (a :* b) `k` r

inl :: (a `k` r) -> (a `k` r) :* (b `k` r)
join :: (a `k` r) :* (b `k` r) -> (a :* b) `k` r

inPF :: h ((a `k` r) -> h (a `k` r))
joinPF :: h (a `k` r) -> (h a `k` r)

need :: h ((a `k` r) -> (h a `k` r))
need = (joinPF .) <$> inPF

need' :: h ((a `k` r) -> (h a `k` r))
need' = (joinPF .) <$> inPF

#endif

-- need :: (IxCoproductPCat k h)
--      => h ((a `k` r) -> (h a `k` r))
-- need = (joinPFF .) <$> inPF
