module ISpec(Field(..),
             Type(..),
             Val(..),
             TVal(..),
             Enumeration(..),
             VarCategory(..),
             Var(..),
             Goal(..),
             Expr(..),
             scalars,
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
             cfaInsTransMany,
             cfaInsTrans',
             cfaInsTransMany',
             Statement(..),
             (=:),
             nop,
             Transition(..),
             wp,
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

-- Value
data Val = BoolVal   Bool
         | IntVal    Integer
         | EnumVal   String
         | PtrVal    LExpr
--         | ArrayVal  [TVal]

data TVal = TVal {ttyp::Type, tval::Val}

data Enumeration = Enumeration { enumName  :: String
                               , enumEnums :: [String]
                               }

data VarCategory = VarState
                 | VarTmp

data Var = Var { varMem  :: Bool
               , varCat  :: VarCategory
               , varName :: String
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
          | ESlice  Expr Slice

-- Extract all scalars from expression
scalars :: Expr -> Type -> [Expr]
scalars e (Struct fs)  = concatMap (\(Field n t) -> scalars (EField e n) t) fs
scalars e (Array  t s) = concatMap (\i -> scalars (EIndex e (EConst $ IntVal $ fromIntegral i)) t) [0..s-1]
scalars e t = [e]

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

cfaInsTransMany :: Loc -> Loc -> [Statement] -> CFA -> CFA
cfaInsTransMany from to stats cfa = cfaInsTrans aft to nop cfa'
    where (cfa', aft) = foldl' (\(cfa, loc) stat -> let (cfa',loc') = cfaInsLoc LNone cfa
                                                    in (cfaInsTrans loc loc' stat cfa', loc'))
                               (cfa, from) stats

cfaInsTrans' :: Loc -> Statement -> CFA -> (CFA, Loc)
cfaInsTrans' from stat cfa = (cfaInsTrans from to stat cfa', to)
    where (cfa', to) = cfaInsLoc LNone cfa

cfaInsTransMany' :: Loc -> [Statement] -> CFA -> (CFA, Loc)
cfaInsTransMany' from stats cfa = (cfaInsTransMany from to stats cfa', to)
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
