{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DefaultSignatures #-}

{-# OPTIONS_GHC -Wall #-}

-- | SMT category built on z3, as first suggested and implemented by John
-- Wiegley with some implementation help from me (Conal). See
-- <https://github.com/jwiegley/z3cat> and John's blog post
-- <http://newartisans.com/2017/04/haskell-and-z3/>. The version in this module
-- is a re-implementation z3cat and works by converting from the circuit graph
-- category rather than as a category of its own. I had a hunch that it’d come
-- out more simply this way, and I think it did. GLSL generation works in the
-- same way.

module ConCat.SMT (solve,EvalE,solveAscending,predValToPred) where

import Prelude hiding (id,(.),const)

import Data.Monoid ((<>))
import Data.Foldable (toList)
import Control.Applicative (liftA2)
import Data.List (sort,unfoldr)
import qualified Data.Map as M
import Data.Sequence (Seq,singleton)

import System.IO.Unsafe (unsafePerformIO)

import Control.Monad.State (StateT,runStateT,execStateT,get,gets,put,modify,lift)

import Z3.Monad

import ConCat.Misc ((:*))
import ConCat.Rep (HasRep(..))
import ConCat.AltCat
import ConCat.Circuit (Comp(..),Bus(..),Ty(..),busTy,GenBuses(..),(:>),mkGraph,pattern CompS)

type E = AST

type M = StateT (M.Map Bus E) Z3

-- TODO: change back to IO (Maybe a), and inquire about deterministism

-- | Build and solve an SMT problem
solve :: forall a. (GenBuses a, EvalE a) => (a :> Bool) -> Maybe a
solve p = unsafePerformIO $ -- Since evalZ3 is presumably deterministic
  evalZ3 $ do
  do is <- genVars (ty @a)
     m  <- execStateT (mapM_ addComp mids) (M.fromList (busesIn `zip` is))
     assert (m M.! res)              -- Make it so!
     snd <$> withModel (`evalEs` is) -- Extract argument value
 where
   (CompS _ "In" [] busesIn,mids, CompS _ "Out" [res] _) =
     splitComps (sort (mkGraph p))

addComp :: Comp -> M ()
addComp (CompS _ prim ins [o]) = do es <- mapM busE ins
                                    e  <- lift $ app prim es (busTy o)
                                    modify (M.insert o e)
addComp comp = error ("ConCat.SMT.addComp: unexpected subgraph comp " ++ show comp)

busE :: Bus -> M E
busE b = gets (M.! b)

app :: String -> [E] -> Ty -> Z3 E
app str [] t = constExpr t str
app nm es _ =
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
    "if"     -> app3  mkIte
    fun      -> error ("ConCat.SMT.app: not supported: " ++ show fun)
 where
   err str = error ("app " ++ nm ++ ": expecting " ++ str ++ " but got " ++ show es)
   app1 op | [e] <- es = op e
           | otherwise = err "one argument"
   app2 op | [e1,e2] <- es = op e1 e2
           | otherwise = err "two arguments"
   app2l op = app2 (\ a b -> op [a,b])
   app3 op | [e1,e2,e3] <- es = op e1 e2 e3
           | otherwise = err "three arguments"

constExpr :: Ty -> String -> Z3 E
constExpr Bool   = mkBool    . read
constExpr Int    = mkIntNum  . read @Int
constExpr Float  = mkRealNum . read @Float
constExpr Double = mkRealNum . read @Double
constExpr t      = error ("ConCat.SMT.constExpr: unexpected literal type: " ++ show t)

mkNeq :: MonadZ3 z3 => E -> E -> z3 E
mkNeq a b = mkNot =<< mkEq a b

{--------------------------------------------------------------------
    Adapted from z3cat
--------------------------------------------------------------------}

genVars :: Ty -> Z3 [E]
genVars = (fmap.fmap) toList go
 where
   -- Seq for efficient (<>)
   go :: Ty -> Z3 (Seq E)
   go Unit       = return mempty
   go Bool       = genPrim mkFreshBoolVar
   go Int        = genPrim mkFreshIntVar
   go Float      = genPrim mkFreshRealVar
   go Double     = genPrim mkFreshRealVar
   go (Prod a b) = liftA2 (<>) (go a) (go b)
   go t          = error ("ConCat.SMT.go: " ++ show t)

genPrim :: (String -> Z3 AST) -> Z3 (Seq E)
genPrim mk = singleton <$> mk "x"

type EvalM = StateT [E] Z3

-- Assemble a list of Es into a value.
class EvalE a where
  evalE :: Model -> EvalM a
  default evalE :: (HasRep a, EvalE (Rep a)) => Model -> EvalM a
  evalE = (fmap.fmap) abst evalE

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

instance (EvalE a, EvalE b, EvalE c) => EvalE (a,b,c)
instance (EvalE a, EvalE b, EvalE c, EvalE d) => EvalE (a,b,c,d)
-- etc

{--------------------------------------------------------------------
    Constrained optimization via iterated satisfaction
--------------------------------------------------------------------}

-- Convert constrained optimization into a predicate for solving.
predValToPred :: Eq r => (a -> Bool :* r) -> (a :* r -> Bool)
predValToPred h (a,r') = b && r' == r where (b,r) = h a
{-# INLINE predValToPred #-}

-- solveAscending' :: ( GenBuses a, GenBuses r, EvalE (a :* r)
--                    , OrdCat (:>) r, ConstCat (:>) r )
--                 => (a :> Bool :* r) -> [a :* r]
-- solveAscending' h = solveAscending (\ (a,r') -> let (b,r) = h a in b && r' == r)

solveAscending :: ( GenBuses a, GenBuses r, EvalE (a :* r)
                  , OrdCat (:>) r, ConstCat (:>) r )
               => (a :* r :> Bool) -> [a :* r]
solveAscending q = maybe [] (\ (a,r) -> (a,r) : solveAscendingFrom q r) (solve q)

solveAscendingFrom :: forall a r. ( GenBuses a, GenBuses r, EvalE (a :* r)
                                  , OrdCat (:>) r, ConstCat (:>) r )
                => (a :* r :> Bool) -> r -> [a :* r]
solveAscendingFrom q = unfoldr (fmap (id &&& exr) . solve . andAbove q)

-- andAbove f lower = \ (a,r) -> f (a,r) && r > lower
andAbove :: forall k a r. (ConstCat k r, OrdCat k r, Ok k a)
         => ((a :* r) `k` Bool) -> r -> ((a :* r) `k` Bool)
andAbove f lower = andC . (greaterThan . (exr &&& const lower) &&& f)
  <+ okProd @k @a    @r
  <+ okProd @k @r    @r
  <+ okProd @k @Bool @Bool

#if 0

-- andAbove:

                       const lower  :: a :* r :> r
               exr &&& const lower  :: a :* r :> r :* r
greaterThan . (exr &&& const lower) :: a :* r :> (a :* r) :* r

-- solveAscendingFrom:

                                     andAbove q  :: r -> (a :* r :> Bool)
                             solve . andAbove q  :: r -> Maybe (a :* r)
         fmap (id &&& exr) . solve . andAbove q  :: r -> Maybe ((a :* r) :* r)
         fmap (id &&& exr) . solve . andAbove q  :: r -> Maybe ((a :* r) :* r)
unfoldr (fmap (id &&& exr) . solve . andAbove q) :: r -> [a :* r]

#endif

-- TODO: Replace a :* r with b, and give an ordering, maybe as b -> o for some
-- ordered o.

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
