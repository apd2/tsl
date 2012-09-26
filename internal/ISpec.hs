module ISpec(Type(..),
             Val(..),
             Enumeration(..),
             Var(..),
             Expr(..),
             disj,
             conj,
             true,
             false,
             (===),
             Loc,
             LocLabel(..),
             CFA,
             newCFA,
             cfaInitLoc,
             cfaErrLoc,
             cfaInsLoc,
             cfaInsTrans,
             Statement(..),
             (=:),
             nop,
             Process(..)) where

import Data.List
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G
import qualified Data.Map as M

import Common

data Field = Field String Type

data Type = Bool
          | SInt     Int
          | UInt     Int
          | Enum     String
          | Struct   [Field]
          | Ptr      Type
          | Array    Type Int
          | FlexType


-- Value
data Val = BoolVal   Bool
         | IntVal    Integer
         | StructVal (M.Map String TVal)
         | EnumVal   String
         | PtrVal    LExpr
         | ArrayVal  [TVal]
         | NondetVal

data TVal = TVal {ttyp::Type, tval::Val}

data Enumeration = Enumeration { enumName  :: String
                               , enumEnums :: [String]
                               }

data Var = Var { varName :: String
               , varType :: Type
               }

data Transition = Transition { tranFrom :: Loc
                             , tranTo   :: Loc
                             , tranCFA  :: CFA
                             }

data Process = Process { procName  :: String
                       , procBody  :: [Transition]
                       , procFinal :: [Loc]  -- final locations
                       }

data Goal = Goal { goalName :: String
                 , goalCond :: Expr
                 }

data Expr = EVar    String
          | EConst  Val
          | EField  Expr String
          | EIndex  Expr Expr
          | EUnOp   UOp Expr
          | EBinOp  BOp Expr Expr
          | ECond   [(Expr, Expr)]
          | ESlice  Expr Slice
          | EStruct String [Expr]
          | ENonDet

(===) :: Expr -> Expr -> Expr
e1 === e2 = EBinOp Eq e1 e2

disj :: [Expr] -> Expr
disj [] = false
disj es = foldl' (\e1 e2 -> EBinOp Or e1 e2) (head es) (tail es)

conj :: [Expr] -> Expr
conj [] = false
conj es = foldl' (\e1 e2 -> EBinOp And e1 e2) (head es) (tail es)

true = EConst $ BoolVal True
false = EConst $ BoolVal False

type Slice = (Int, Int)

type LExpr = Expr

-- Atomic statement
data Statement = SAssume Expr
               | SAssign Expr Expr

(=:) :: Expr -> Expr -> Statement
(=:) e1 e2 = SAssign e1 e2

nop :: Statement
nop = SAssume $ true

-- Control-flow automaton
type Loc = G.Node
data LocLabel = LNone | LPause | LFinal
type CFA = G.Gr LocLabel Statement

newCFA :: CFA
newCFA = G.insNode (1,LPause) $ G.insNode (0,(LPause)) G.empty

cfaErrLoc :: Loc
cfaErrLoc = 0

cfaInitLoc :: Loc
cfaInitLoc = 1

cfaInsLoc :: LocLabel -> CFA -> (CFA, Loc)
cfaInsLoc lab cfa = (G.insNode (loc,lab) cfa, loc)
   where loc = (snd $ G.nodeRange cfa) + 1

cfaInsTrans :: Loc -> Loc -> Statement -> CFA -> CFA
cfaInsTrans from to stat cfa = G.insEdge (from,to,stat) cfa

data Spec = Spec { specEnum         :: [Enumeration]
                 , specVar          :: [Var]
                 , specProcess      :: [Process]
                 , specInit         :: Expr
                 , specGoal         :: [Goal] 
                 }
