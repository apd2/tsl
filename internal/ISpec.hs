module ISpec(Field(..),
             Type(..),
             Val(..),
             TVal(..),
             Enumeration(..),
             Var(..),
             Goal(..),
             Expr(..),
             disj,
             conj,
             true,
             false,
             (===),
             Loc,
             LocLabel(..),
             isDelayLabel,
             CFA,
             newCFA,
             cfaInitLoc,
             cfaErrLoc,
             cfaInsLoc,
             cfaLocLabel,
             cfaInsTrans,
             cfaInsTrans',
             Statement(..),
             (=:),
             nop,
             Transition(..),
             wp,
             isTmpVar,
             exprVars,
             Spec(..)) where

import Data.List
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G
import qualified Data.Map as M

import Util hiding (name)
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
data LocLabel = LNone 
              | LPause Expr
              | LFinal 
type CFA = G.Gr LocLabel Statement

isDelayLabel :: LocLabel -> Bool
isDelayLabel (LPause _) = True
isDelayLabel LFinal     = True
isDelayLabel LNone      = False

newCFA :: Expr -> CFA
newCFA initcond = G.insNode (cfaInitLoc,LPause initcond) $ G.insNode (cfaErrLoc,(LPause false)) G.empty

cfaErrLoc :: Loc
cfaErrLoc = 0

cfaInitLoc :: Loc
cfaInitLoc = 1

cfaInsLoc :: LocLabel -> CFA -> (CFA, Loc)
cfaInsLoc lab cfa = (G.insNode (loc,lab) cfa, loc)
   where loc = (snd $ G.nodeRange cfa) + 1

cfaLocLabel :: Loc -> CFA -> LocLabel
cfaLocLabel loc cfa = fromJustMsg "cfaLocLabel" $ G.lab cfa loc

cfaInsTrans :: Loc -> Loc -> Statement -> CFA -> CFA
cfaInsTrans from to stat cfa = G.insEdge (from,to,stat) cfa

cfaInsTrans' :: Loc -> Statement -> CFA -> (CFA, Loc)
cfaInsTrans' from stat cfa = (cfaInsTrans from to stat cfa', to)
    where (cfa', to) = cfaInsLoc LNone cfa

data Spec = Spec { specEnum         :: [Enumeration]
                 , specVar          :: [Var]
                 , specCTran        :: [Transition]
                 , specUTran        :: [Transition]
                 , specWire         :: Transition
                 , specInit         :: Expr
                 , specGoal         :: [Goal] 
                 , specFair         :: [Expr]           -- sets of states f s.t. GF(-f)
                 }

wp :: Expr -> [Transition] -> Expr
wp _ _ = error "Not implemented: wp"

isTmpVar :: Var -> Bool
isTmpVar _ = error "Not implemented: isTmpVar"

exprVars :: Expr -> [Var]
exprVars _ = error "Not implemented: exprVars"
