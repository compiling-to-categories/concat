{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.GLSL where

import qualified Data.Map as M
import System.Directory (createDirectoryIfMissing)

import Text.PrettyPrint.HughesPJClass -- (Pretty,prettyShow)
import Language.GLSL.Syntax
import Language.GLSL.Pretty

import ConCat.Circuit
  (CompS(..),PinId,Bus(..),GenBuses,(:>), GraphInfo, mkGraph, unitize)
import qualified ConCat.Circuit as C

fromCirc :: GenBuses a => String -> (a :> b) -> (String,ExternalDeclaration)
fromCirc name0 circ =
  ( name
  , FunctionDefinition
      (FuncProt (FullType Nothing
                 (TypeSpec Nothing 
                  (TypeSpecNoPrecision Void Nothing)))
       "main" []) 
      (Compound (fromCompS <$> comps)))
 where
   (name,compDepths,_report) = mkGraph name0 (unitize circ)
   comps :: [CompS]
   comps = M.keys compDepths 

runCirc :: GenBuses a => String -> (a :> b) -> IO ()
runCirc name0 circ =
  do createDirectoryIfMissing False outDir
     writeFile (outDir++"/"++name++".frag") (prettyShow decl)
 where
   (name,decl) = fromCirc name0 circ
   outDir = "out"

#if 0

mkGraph :: Name -> UU -> GraphInfo
type GraphInfo = (Name,CompDepths,Report)
type CompDepths = Map CompS Depth

#endif

#if 0
data ExternalDeclaration =
    -- function declarations should be at top level (page 28)
    FunctionDeclaration FunctionPrototype
  | FunctionDefinition FunctionPrototype Compound
  | Declaration Declaration
  deriving (Show, Eq)

data FunctionPrototype = FuncProt FullType String [ParameterDeclaration]

data FullType = FullType (Maybe TypeQualifier) TypeSpecifier

data TypeSpecifier = TypeSpec (Maybe PrecisionQualifier) TypeSpecifierNoPrecision

data TypeSpecifierNoPrecision = TypeSpecNoPrecision TypeSpecifierNonArray (Maybe (Maybe Expr)) -- constant expression
#endif

fromCompS :: CompS -> Statement
fromCompS (CompS _n prim ins [Bus pid ty] _) =
  DeclarationStatement (
   InitDeclaration (TypeDeclarator
                    (FullType Nothing
                     (TypeSpec Nothing
                      (TypeSpecNoPrecision (glslTy ty) Nothing))))
     [InitDecl (varName pid) Nothing (Just (prim `app` ins))])
fromCompS comp =
  error ("ConCat.GLSL.fromCompS: not supported: " ++ show comp)

glslTy :: C.Ty -> TypeSpecifierNonArray
glslTy C.Int   = Int
glslTy C.Bool  = Bool
glslTy C.Float = Float
glslTy ty = error ("ConCat.GLSL.glslTy: unsupported type: " ++ show ty)

varName :: PinId -> String
varName pid = "x" ++ show pid

app :: String -> [Bus] -> Expr
app "+" [b1,b2] = Add (bToE b1) (bToE b2)
app fun args =
  error ("ConCat.GLSL.app: not supported: " ++ show (fun,args))
  
bToE :: Bus -> Expr
bToE (Bus pid _width) = Variable (varName pid)
