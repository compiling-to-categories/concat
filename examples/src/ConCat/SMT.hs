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
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | SMT category built on z3. A re-implementation of
-- <https://github.com/jwiegley/z3cat>, which is described at
-- <http://newartisans.com/2017/04/haskell-and-z3/>

module ConCat.SMT (solve,GenE(..),EvalE(..)) where

import Control.Applicative (liftA2)
import Data.List (sort)
import qualified Data.Map as M

import Control.Monad.State (StateT,runStateT,execStateT,get,gets,put,modify,lift)

import Z3.Monad

import ConCat.AltCat (Ok)
import ConCat.Circuit (Comp(..),Bus(..),Ty(..),busTy,(:>),mkGraph,pattern CompS)

type E = AST

type M = StateT (M.Map Bus E) Z3

busE :: Bus -> M E
busE b = gets (M.! b)

solve :: forall a. (Ok (:>) a, GenE a, EvalE a) => (a :> Bool) -> IO (Maybe a)
solve p =
  -- evalZ3With Nothing (opt "MODEL" True) $ do
  evalZ3 $ do
  do is <- genE @a
     m  <- execStateT (mapM_ addComp mids) (M.fromList (busesIn `zip` is))
     assert (m M.! res)
     -- check and get solution
     snd <$> withModel (`evalEs` is)
 where
   (CompS _ "In" [] busesIn,mids, CompS _ "Out" [res] _) =
     splitComps (sort (mkGraph p))

addComp :: Comp -> M ()
addComp (CompS _ str [] [o]) = do res <- lift (constExpr (busTy o) str)
                                  modify (M.insert o res)
addComp (CompS _ prim ins [o]) = do es  <- mapM busE ins
                                    res <- lift (app prim es)
                                    modify (M.insert o res)
addComp comp = error ("ConCat.SMT.addComp: unexpected subgraph comp " ++ show comp)

-- TODO: refactor addComp

constExpr :: Ty -> String -> Z3 E
constExpr Bool    = mkBool    . read
constExpr Int     = mkIntNum  . read @Int
constExpr Float   = mkRealNum . read @Float
constExpr Double  = mkRealNum . read @Double
constExpr ty      = error ("ConCat.SMT.constExpr: unexpected literal type: " ++ show ty)

app :: String -> [E] -> Z3 E
app nm es =
  case nm of
    "not"    -> app1  mkNot
    "&&"     -> app2l mkAnd
    "||"     -> app2l mkOr
    "<"      -> app2  mkLt
    ">"      -> app2  mkGt
    "<="     -> app2  mkLe
    ">="     -> app2  mkGe
    "=="     -> app2  mkEq
    "/="     -> app2  mkNeq
    "negate" -> app1  mkUnaryMinus
    "+"      -> app2l mkAdd
    "-"      -> app2l mkSub
    "*"      -> app2l mkMul
    "/"      -> app2  mkDiv
    "mod"    -> app2  mkMod
    "xor"    -> app2  mkNeq
    fun      -> error ("ConCat.SMT.app: not supported: " ++ show fun)
 where
   err str = error ("app " ++ nm ++ ": expecting " ++ str ++ " but got " ++ show es)
   app1 op | [e] <- es = op e
           | otherwise = err "one argument"
   app2 op | [e1,e2] <- es = op e1 e2
           | otherwise = err "two arguments"
   app2l op = app2 (\ a b -> op [a,b])

mkNeq :: MonadZ3 z3 => E -> E -> z3 E
mkNeq a b = mkNot =<< mkEq a b

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

-- genTy :: Ty -> Z3 [E]
-- genTy Unit       = return []
-- genTy Bool       = genPrim mkFreshBoolVar
-- genTy Int        = genPrim mkFreshIntVar
-- genTy Float      = genPrim mkFreshRealVar
-- genTy Double     = genPrim mkFreshRealVar
-- genTy (Prod a b) = liftA2 (++) (genTy a) (genTy b)
-- genTy ty         = error ("ConCat.SMT.genTy: " ++ show ty)

-- -- TODO: replace genE with genTy and combine with ty from circuit


-- TODO: Use Seq in place of [] in genE, and compare efficiency.

type EvalM = StateT [E] Z3

-- Assemble a list of Es into a value.
class EvalE a where evalE :: Model -> EvalM a

evalEs :: EvalE a => Model -> [E] -> Z3 a
evalEs model es = do (a,[]) <- runStateT (evalE model) es
                     return a

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
