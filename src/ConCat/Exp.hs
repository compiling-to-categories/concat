{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Exp
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Lambda expressions
----------------------------------------------------------------------

-- Whether to sugar during show, including 'let'
#define Sugared

module ConCat.Exp where

-- TODO: Explicit exports

import Control.Arrow (first)
import Data.Maybe (fromMaybe,catMaybes,listToMaybe)
import Data.Char (isDigit)
import Data.Type.Equality ((:~:)(..),TestEquality(..))
import Data.Functor.Classes (Show1(..))
import Unsafe.Coerce (unsafeCoerce)
import System.IO.Unsafe (unsafePerformIO)  -- experiment

import qualified Data.Map as M
-- import Debug.Trace

-- transformers
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State

import ConCat.Misc (Unop,(:*),Evalable(..),(====){-,Eq1'(..)-},PrimBasics(..))
import ConCat.ShowUtils

-- | Variable names
type Name = String

-- | Typed variable. Phantom
data V a = V Name

instance Show (V a) where
  showsPrec _ (V n) = showString n

varName :: V a -> Name
varName (V name) = name

instance TestEquality V where
  V a `testEquality` V b | a == b    = unsafeCoerce (Just Refl)
                         | otherwise = Nothing

-- TODO: make TestEquality V safer by adding a Typeable constraint to V and
-- using it.

infixr 1 :$
infixr 8 :@

-- | Binding patterns
data Pat :: * -> * where
  UnitPat :: Pat ()
  VarPat  :: V a -> Pat a
  (:$)    :: Pat a -> Pat b -> Pat (a :* b)
  (:@)    :: Pat a -> Pat a -> Pat a

-- NOTE: ":@" is named to suggest "as patterns", but is more general ("and patterns").

-- TODO: Rename UnitPat and VarPat to PUnit and PVar

instance Show (Pat a) where
  showsPrec _ UnitPat     = showString "()"
  showsPrec p (VarPat v)  = showsPrec p v
  showsPrec p (a :$ b)    = showsPair p a b
  showsPrec p (a :@ b)    = showsOp2 False "@" (8,AssocRight) p a b

infixl 9 :^
-- | Lambda expressions
data E :: (* -> *) -> (* -> *) where
  Var     :: V a -> E p a
  ConstE  :: p a -> E p a
  (:^)    :: E p (a -> b) -> E p a -> E p b
  Lam     :: Pat a -> E p b -> E p (a -> b)

-- letE :: Pat a -> E p a -> E p b -> E p b
-- letE q rhs body = (Lam q body) :^ rhs

letPair :: Name -> Name -> E p c -> E p (a :* b -> c)
letPair a b = Lam (VarPat (V a) :$ VarPat (V b)) 

{--------------------------------------------------------------------
    Show
--------------------------------------------------------------------}

intercalateShows :: Foldable f => ShowS -> f ShowS -> ShowS
intercalateShows gap = foldr1 (\ g f -> g . gap . f)

instance (HasOpInfo prim, Show' prim, TestEquality prim, PrimBasics prim) => Show (E prim a) where
#ifdef Sugared
--   showsPrec p (Either (Lam q a) (Lam r b) :^ ab) =
--     showParen (p > 0) $
--     showString "case " . shows ab . showString " of { "
--                        . shows q . showString " -> " . shows a . showString " ; "
--                        . shows r . showString " -> " . shows b . showString " } "
  showsPrec p e@(Lam {} :^ _) =  -- beta multi-redex as "let"
    showParen (p > 0) $
    showString "let " . shBinds binds . showString " in " . body
   where
     (binds,body) = collect e
     collect :: E prim b -> ([ShowS],ShowS)
     collect (Lam q e' :^ rhs) =
       first ((shows q . showString " = " . shows rhs) :) (collect e')
     collect e'                = ([],shows e')
     shBinds [b] = b
     shBinds bs  = showString "{ "
                 . intercalateShows (showString "; ") bs
                 . showString " }"
  showsPrec p (ConstE ((==== pairP) -> True) :^ u :^ v)
                          = showsPair p u v
#endif
  showsPrec p (ConstE prim :^ u :^ v) | Just (OpInfo op fixity) <- opInfo prim =
    showsOp2 False op fixity p u v
  showsPrec _ (Var (V n)) = showString n
  showsPrec p (ConstE c)  = showsPrec' p c
  showsPrec p (u :^ v)      = showsApp p u v
  showsPrec p e@(Lam {}) = showParen (p > 0) $
    showString "\\ " . intercalateShows (showString " ") pats
     . showString " -> " . body
   where
     (pats,body) = collect e
      where
        -- Collect shown patterns and body
        collect :: E prim b -> ([ShowS],ShowS)
        collect (Lam q e') = first (shows q :) (collect e')
        collect e'         = ([],shows e')

--   showsPrec p (Either f g) = showsOp2' "|||" (2,AssocRight) p f g
--   showsPrec p (Loop h) = showsApp1 "loop" p h
--   showsPrec p (CoerceE e)  = showsApp1 "coerce" p e

-- TODO: Multi-line pretty printer with indentation

{--------------------------------------------------------------------
    Evaluation
--------------------------------------------------------------------}

evalE :: (HasOpInfo p, Show1 p, Evalable p) =>  -- , Eq1' p, PrimBasics p
         E p a -> a
evalE e = -- trace ("evalE: " ++ show e) $
          eval' e []  -- provide empty environment

-- Expression evaluation requires a binding environment. In other words,
-- expressions evaluate to a function from environments.

-- | Single variable binding
data Bind = forall a. Bind (V a) a
-- | Variable environment
type Env = [Bind]

extendEnv :: Pat b -> b -> (Env -> Env)
extendEnv UnitPat       ()      = id
extendEnv (VarPat vb)   b       = (Bind vb b :)
extendEnv (p :$ q)    (a,b)     = extendEnv q b . extendEnv p a
extendEnv (p :@ q)      b       = extendEnv q b . extendEnv p b
-- extendEnv ZeroPat      Zero     = id
-- extendEnv (SuccPat q)  (Succ m) = extendEnv q m

-- TODO: Rewrite extendEnv so that it examines the pattern just once,
-- independently from the value.

lookupVar :: forall a. V a -> Env -> Maybe a
lookupVar va = listToMaybe . catMaybes . map check
 where
   check :: Bind -> Maybe a
   check (Bind vb b) | Just Refl <- va `testEquality` vb = Just b
                     | otherwise                         = Nothing

eval' :: (HasOpInfo p, Show1 p, Evalable p) => 
         E p a -> Env -> a

eval' (Var v)      env = fromMaybe (error $ "eval': unbound variable: " ++ show v) $
                         lookupVar v env
eval' (ConstE p)   _   = eval p
eval' (u :^ v)     env = (eval' u env) (eval' v env)
eval' (Lam p e)    env = \ x -> eval' e (extendEnv p x env)
-- eval' (Either f g) env = eval' f env `either` eval' g env
-- eval' (Loop h)     env = loop (eval' h env)
-- eval' (CoerceE e)  env = coerce (eval' e env)

-- TODO: Rework so that eval' can work independently of env. Will save repeated
-- evals.

{--------------------------------------------------------------------
    Special expressions
--------------------------------------------------------------------}

reifyE :: a -> E p a
reifyE _ = error "reifyE: Oops -- not eliminated."
{-# NOINLINE reifyE #-}  -- to give reify/eval rules a chance

{--------------------------------------------------------------------
    Clean up variable names
--------------------------------------------------------------------}

-- Max numeric suffix used per simple name
type UsedNames = M.Map Name Int

-- Renaming substitution
type Renamer = M.Map Name Name

type RenameEnv = (UsedNames,Renamer)

type RenameR = Reader RenameEnv
type RenameS = State  RenameEnv

-- Huh?
huh :: a -> a
huh = unsafePerformIO . return

-- Without huh, renameVars calls get removed by the compiler in GHC 7.10.3 and 8.1.
-- Demand changes from <S,U> to <L,U>.
-- 
-- TODO: Understand what's going on here.

renameVars :: forall p a. (Show' p, HasOpInfo p, TestEquality p, PrimBasics p) => Unop (E p a)
renameVars e0 = huh $
                runReader (renameExp e0) mempty
 where
   renameExp :: E p b -> RenameR (E p b)
   -- renameExp e | trace ("renameExp: " ++ show e) False = undefined
   renameExp (Var (V nm)) =
    do (_,renamer) <- ask
       let nm' = fromMaybe (error ("RR.Exp.rename: free variable " ++ show nm
                                   ++ " in expression " ++ show e0))
                   (M.lookup nm renamer)
       return (Var (V nm'))
   renameExp (ConstE p) = return (ConstE p)
   renameExp (u :^ v) = (:^) <$> renameExp u <*> renameExp v
   renameExp (Lam pat body) =
     do env <- ask
        let (pat',env') = runState (renamePat pat) env
        body' <- local (const env') (renameExp body)
        return $ -- trace ("rename lam env = " ++ show env) $
                 -- trace ("rename lam env' = " ++ show env') $
                 Lam pat' body'
   renamePat :: Pat b -> RenameS (Pat b)
   -- renamePat p | trace ("renamePat: " ++ show p) False = undefined
   renamePat UnitPat           = return UnitPat
   renamePat (VarPat (V name)) =
     do (used,renamer) <- get
        let base        = stripName name
            (mbN,used') = M.insertLookupWithKey (const (+)) base 1 used
            name'       = maybe base ((base ++) . show) mbN
            renamer'    = M.insert name name' renamer
        put (used',renamer')
        return $ VarPat (V name')
   renamePat (u :$ v) = (:$) <$> renamePat u <*> renamePat v
   renamePat (u :@ v) = (:@) <$> renamePat u <*> renamePat v
{-# NOINLINE renameVars #-}

-- Names look like foo_suff. Drop the suffix and then any trailing digits.
-- Keep consistent with fqVarName in Plugin.
stripName :: Unop Name
stripName name = reverse
               . dropWhile isDigit 
               . tail' 
               . dropWhile (/= '_') 
               . reverse
               $ name
 where
   tail' [] = error ("stripName: missing suffix in " ++ show name)
   tail' (_:cs) = cs
