{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ParallelListComp #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fdefer-typed-holes #-} -- TEMP

-- | 

module ConCat.GLSL where

import Control.Monad (when)
import Data.Ord (comparing)
import Data.List (sortBy)
import Data.Either (rights)
import qualified Data.Map as M
import System.Directory (createDirectoryIfMissing)

import Text.ParserCombinators.Parsec (runParser,ParseError,GenParser)

import Text.PrettyPrint.HughesPJClass -- (Pretty,prettyShow)
import Language.GLSL.Syntax
import Language.GLSL.Pretty

import Language.GLSL.Parser hiding (parse)

import ConCat.Circuit
  ( CompS(..),compName,PinId(..),Bus(..),GenBuses,(:>)
  , GraphInfo, mkGraph, unitize)
import qualified ConCat.Circuit as C
import ConCat.Misc ((:*))

type Im = Float :* Float :> Bool

type OkIm a b = (a :> b) ~ Im

showGraph :: Bool
showGraph = True -- False

-- Phase out, and rename genGlsl'
genGlsl :: String -> Im -> IO ()
genGlsl name0 circ =
  do createDirectoryIfMissing False outDir
     writeFile (outDir++"/"++name++".frag")
       (unlines prelude ++ prettyShow statements ++ "\n")
 where
   (name,statements) = fromCirc name0 circ
   outDir = "out"

genGlsl' :: String -> Im -> IO ()
genGlsl' name0 circ =
  do when showGraph $ putStrLn $ "genGlsl: Graph \n" ++ show g
     createDirectoryIfMissing False outDir
     writeFile (outDir++"/"++name++".frag")
       (prettyShow fundef ++ "\n")
 where
   g@(name,compDepths,_report) = mkGraph name0 (unitize circ)
   comps = sortBy (comparing C.compNum) (M.keys compDepths)
   fundef = fromComps comps
   outDir = "out"

-- TEMP hack: wire in parameters
prelude :: [String]
prelude =
  [ "bool effect (vec2 _point)"
  ]

fromCirc :: String -> Im -> (String,Compound)
fromCirc name0 circ =
  (name, Compound (concat (fromComp . unCompS <$> (i : mid ++ [o]))))
 where
   (name,compDepths,_report) = mkGraph name0 (unitize circ)
   (i,mid,o) = splitComps (sortBy (comparing C.compNum) (M.keys compDepths))

unCompS :: CompS -> (String,[Bus],[Bus])
unCompS (CompS _ fun ins outs _) = (fun,ins,outs)

fromComps :: [CompS] -> ExternalDeclaration
fromComps comps =
  funDef Bool "effect" (paramDecl <$> inputs)
         (concat (fromComp . unCompS <$> (mid ++ [o])))
 where
   (unCompS -> ("In",[],inputs),mid,o) = splitComps comps

paramDecl :: Bus -> ParameterDeclaration
paramDecl (Bus pid ty) =
  ParameterDeclaration Nothing Nothing 
    (TypeSpec Nothing (TypeSpecNoPrecision (glslTy ty) Nothing))
    (Just (varName pid,Nothing))

funDef :: TypeSpecifierNonArray -> String -> [ParameterDeclaration]
       -> [Statement] -> ExternalDeclaration
funDef resultTy name params statements =
  FunctionDefinition (
    FuncProt (FullType Nothing
              (TypeSpec Nothing (TypeSpecNoPrecision resultTy Nothing)))
             name params)
    (Compound statements)

fromComp :: (String,[Bus],[Bus]) -> [Statement]
-- fromComp ("In",[],[x,y]) = defXY x y
fromComp ("Out",[b],[]) = [Return (Just (bToE b))]
fromComp (str,[],[b@(Bus _ ty)]) =
  [initBus b (
     case ty of
       C.Bool  -> BoolConstant        (read str)
       C.Int   -> IntConstant Decimal (read str)
       C.Float -> FloatConstant       (read str)
       _ -> error ("ConCat.GLSL.fromComp: unexpected literal type: " ++ show ty))]
fromComp (prim,ins,[b]) = [initBus b (app prim (bToE <$> ins))]
fromComp comp =
  error ("ConCat.GLSL.fromComp: not supported: " ++ show comp)

initBus :: Bus -> Expr -> Statement
initBus (Bus pid ty) e = initDecl (glslTy ty) (varName pid) e

assign :: String -> Expr -> Statement
assign v e = ExpressionStatement (Just (Equal (Variable v) e))

initDecl :: TypeSpecifierNonArray -> String -> Expr -> Statement
initDecl ty var e =
 DeclarationStatement (
  InitDeclaration (
      TypeDeclarator (
          FullType Nothing (TypeSpec Nothing (TypeSpecNoPrecision ty Nothing))))
  [InitDecl var Nothing (Just e)])


glslTy :: C.Ty -> TypeSpecifierNonArray
glslTy C.Int   = Int
glslTy C.Bool  = Bool
glslTy C.Float = Float
glslTy ty = error ("ConCat.GLSL.glslTy: unsupported type: " ++ show ty)

varName :: PinId -> String
varName (PinId n) = "v" ++ show n

app :: String -> [Expr] -> Expr
app "+" [e1,e2] = Add e1 e2
app ">" [e1,e2] = Gt  e1 e2
app fun args =
  error ("ConCat.GLSL.app: not supported: " ++ show (fun,args))

  
bToE :: Bus -> Expr
bToE (Bus pid _ty) = Variable (varName pid)

unsnoc :: [a] -> ([a],a)
unsnoc as = (mid,o) where (mid,[o]) = splitAt (length as - 1) as

-- Extract input, middle, output components
splitComps :: [CompS] -> (CompS,[CompS],CompS)
splitComps (i@(CompS 0 "In" [] _ _) : (unsnoc -> (mid,o))) = (i,mid,o)
splitComps comps = error ("ConCat.GLSL.splitComps: Oops: " ++ show comps)

-- For experiments
parse :: P a -> String -> Either ParseError a
parse p = runParser p S "GLSL"

selectField :: String -> String -> Expr
selectField var field = FieldSelection (Variable var) field

defXY :: Bus -> Bus -> [Statement]
defXY (Bus x C.Float) (Bus y C.Float) =
  [ initDecl Float (varName v) (selectField "_point" field)
  | v <- [x,y] | field <- ["x","y"]]
defXY bx by = error ("ConCat.GLSL.defXY: oops: " ++ show (bx,by))
