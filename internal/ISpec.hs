module ISpec(Expr(..),
             Loc,
             CFA) where

import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G
import qualified Data.Map as M

import Common

data Field = Field String TypeSpec

data TypeSpec = BoolSpec
              | SIntSpec     Int
              | UIntSpec     Int
              | StructSpec   [Field]
              | PtrSpec      TypeSpec
              | ArraySpec    TypeSpec Int
              | FlexTypeSpec


-- Value
data Val = BoolVal   Bool
         | IntVal    Integer
         | StructVal (M.Map String TVal)
         | EnumVal   String
         | PtrVal    LExpr
         | ArrayVal  [TVal]
         | NondetVal

data TVal = TVal {ttyp::TypeSpec, tval::Val}

data Enumeration = Enumeration { enumName  :: String
                               , enumEnums :: [String]
                               }

data Var = Var { varName :: String
               , varType :: TypeSpec
               }

data Process = Process { procName :: String
                       , procBody :: Statement
                       }

data Goal = Goal { goalName :: String
                 , goalCond :: Expr
                 }

data Expr = EVar    String
          | EConst  Val
          | EBool   Bool
          | EField  Expr String
          | EIndex  Expr Expr
          | EUnOp   UOp Expr
          | EBinOp  BOp Expr Expr
          | ECond   [(Expr, Expr)]
          | ESlice  Expr Slice
          | EStruct String [Expr]
          | ENonDet

type Slice = (Int, Int)

type LExpr = Expr

-- Atomic statement
data Statement = SPause   
               | SStop    
               | SLabel  String [(String, Expr)]
               | SAssert Expr
               | SAssume Expr
               | SAssign Expr Expr
               | SMagic  (Either String Expr)


-- Control-flow automaton
type Loc = Int
type CFA = G.Gr Loc Statement

data Spec = Spec { specEnum         :: [Enumeration]
                 , specVar          :: [Var]
                 , specProcess      :: [Process]
                 , specControllable :: Expr
                 , specInvisible    :: Expr
                 , specInit         :: Statement
                 , specGoal         :: [Goal] 
                 }
