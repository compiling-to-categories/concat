{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ParallelListComp #-}
-- TODO: trim pragmas above
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | SMT category built on z3. A re-implementation of
-- <https://github.com/jwiegley/z3cat>, which is described at
-- <http://newartisans.com/2017/04/haskell-and-z3/>

module ConCat.SMT where

import Control.Applicative (liftA2)
import Data.List (sort)
import qualified Data.Map as M

-- mtl
import Control.Monad.State (StateT,execStateT,get,put,lift)

import Z3.Monad

import ConCat.AltCat (Ok)
import ConCat.Circuit (Comp(..),Bus(..),busTy,(:>),mkGraph,pattern CompS)

type E = AST

type M = StateT (M.Map Bus E) Z3

genSMT :: forall a. (Ok (:>) a, GenE a) => (a :> Bool) -> Z3 E
genSMT p =
  do is <- genE @a
     m  <- execStateT (mapM_ addComp mids) (M.fromList (busesIn `zip` is))
     return (m M.! res)
 where
   (CompS _ "In" [] busesIn,mids, CompS _ "Out" [res] _) =
     splitComps (sort (mkGraph p))

addComp :: Comp -> M ()
addComp = undefined

{--------------------------------------------------------------------
    Modified from z3cat
--------------------------------------------------------------------}

class GenE a where genE :: Z3 [E]

genPrim :: (String -> Z3 AST) -> Z3 [E]
genPrim mk = (:[]) <$> mk "x"

instance GenE ()     where genE = return []
instance GenE Bool   where genE = genPrim mkFreshBoolVar
instance GenE Int    where genE = genPrim mkFreshIntVar
instance GenE Float  where genE = genPrim mkFreshRealVar
instance GenE Double where genE = genPrim mkFreshRealVar

instance (GenE a, GenE b) => GenE (a,b) where
  genE = liftA2 (++) (genE @a) (genE @b)

-- TODO: Use Seq in place of [] in genE, and compare efficiency.

type EvalM = StateT [E] Z3

-- Assemble a list of Es into a value.
class EvalE a where evalE :: Model -> EvalM a

-- type EvalAst m a = Model -> AST -> m (Maybe a)

evalPrim :: EvalAst Z3 a' -> (a' -> a) -> Model -> EvalM a
evalPrim ev f m =
  do es <- get
     case es of
       []      -> fail "evalPrim: exhausted ASTs"
       (e:es') -> do Just a' <- lift (ev m e)
                     put es'
                     return (f a')

instance EvalE ()     where evalE = evalPrim evalBool (const ())
instance EvalE Bool   where evalE = evalPrim evalBool id
instance EvalE Int    where evalE = evalPrim evalInt  fromInteger
instance EvalE Float  where evalE = evalPrim evalReal fromRational
instance EvalE Double where evalE = evalPrim evalReal fromRational

instance (EvalE a, EvalE b) => EvalE (a,b) where
    evalE m = liftA2 (,) (evalE m) (evalE m)

{--------------------------------------------------------------------
    Copied from GLSL. Move to Circuit.
--------------------------------------------------------------------}

-- Extract input, middle, output components. 
-- TODO: move sort & mkGraph calls here so that we start with a (:>).

splitComps :: [Comp] -> (Comp,[Comp],Comp)
splitComps (i@(CompS _ "In" [] _)
            : (unsnoc -> (mid,o@(CompS _ "Out" _ [])))) = (i,mid,o)
splitComps comps = error ("ConCat.GLSL.splitComps: Oops: " ++ show comps)

unsnoc :: [a] -> ([a],a)
unsnoc as = (mid,o) where (mid,[o]) = splitAt (length as - 1) as
