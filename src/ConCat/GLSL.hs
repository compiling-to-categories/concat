{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.GLSL where

import Language.GLSL.Syntax

import ConCat.Circuit           -- TODO: trim import list


#if 0
data CompS = CompS CompNum PrimName [Input] [Output] Reuses deriving Show

data Bus = Bus PinId Width

type Input  = Bus
type Output = Bus
#endif

fromCompS :: CompS -> Statement
fromCompS (CompS n prim ins [Bus pid widthToTy] _) =
  DeclarationStatement (
   InitDeclaration (TypeDeclarator
                    (FullType Nothing
                     (TypeSpec Nothing
                      (TypeSpecNoPrecision Int Nothing))))
     [InitDecl (varName pid) Nothing (Just (prim `app` ins))])
fromCompS comp =
  error ("ConCat.GLSL.fromCompS: not supported: " ++ show comp)

-- Temporary hack: assume Bool or Int.
-- I'll need to track actual type.
-- How do/did I get Float vs Int for Verilog?

widthToTy :: Width -> TypeSpecifierNonArray
widthToTy 1  = Bool
widthToTy 32 = Int
widthToTy w  = error ("widthToTy: unsupported width: " ++ show w)

varName :: PinId -> String
varName pid = "x" ++ show pid

app :: String -> [Bus] -> Expr
app "+" [b1,b2] = Add (bToE b1) (bToE b2)
app fun args =
  error ("ConCat.GLSL.app: not supported: " ++ show (fun,args))
  
bToE :: Bus -> Expr
bToE (Bus pid _width) = Variable (varName pid)

#if 0

-- TODO clean
data Declaration =
    InitDeclaration InvariantOrType [InitDeclarator]
  | ...

data FullType = FullType (Maybe TypeQualifier) TypeSpecifier

data TypeSpecifier = TypeSpec (Maybe PrecisionQualifier) TypeSpecifierNoPrecision

data TypeSpecifierNoPrecision = TypeSpecNoPrecision TypeSpecifierNonArray (Maybe (Maybe Expr)) -- constant expression

data InitDeclarator = InitDecl String (Maybe (Maybe Expr)) (Maybe Expr) --

data TypeSpecifierNonArray =
    Void
  | Float
  | Int
  | UInt
  | Bool
  | Vec2
  | Vec3
  | Vec4
  | ...
  deriving (Show, Eq)

#endif
