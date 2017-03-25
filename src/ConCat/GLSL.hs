{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.GLSL where

import Language.GLSL.Syntax

import ConCat.Circuit (CompS(..),PinId,Bus(..))
import qualified ConCat.Circuit as C

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
