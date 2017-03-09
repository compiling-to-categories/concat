{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | First-order, monomorphic expression language with explicit sharing

module ConCat.Expr where

data Extractor :: * -> * -> * where
  Head :: Extractor (a,b) a
  Tail :: Extractor env b -> Extractor (a,env) b

data E :: * -> * -> * where
  App :: Prim doms ran -> Es env doms -> E env ran
  Var :: Extractor env a -> E env a
  Let :: E env a -> E (a,env) b -> E env b

-- data Es :: [*] -> * where
--   Null :: Es '[]
--   Cons :: E a -> Es as -> Es (a:as)

type Es env = Xs (E env)

data Xs :: (u -> *) -> [u] -> * where
  Null :: Xs f '[]
  Cons :: f a -> Xs f as -> Xs f (a:as)

data Prim :: [*] -> * -> * where
  LitP :: a -> Prim '[] a
  NegateP :: Num a => Prim '[a] a
  AddP, SubP, MulP :: Num a => Prim [a,a] a

lit :: a -> E env a
lit a = App (LitP a) Null

