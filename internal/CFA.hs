module CFA(Statement(..),
           (=:),
           nop,
           Loc,
           LocLabel(..),
           CFA,
           isDelayLabel,
           newCFA,
           cfaErrLoc,
           cfaInitLoc,
           cfaInsLoc,
           cfaLocLabel,
           cfaInsTrans,
           cfaInsTransMany,
           cfaInsTrans',
           cfaInsTransMany',
           cfaSuc,
           cfaAddNullPtrTrans) where

import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G
import Data.List
import Data.Tuple

import Util hiding (name)
import IExpr

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

cfaSuc :: Loc -> CFA -> [(Statement,Loc)]
cfaSuc loc cfa = map swap $ G.lsuc cfa loc

-- Add error transitions for all potential null-pointer dereferences
cfaAddNullPtrTrans :: CFA -> Expr -> CFA
cfaAddNullPtrTrans cfa nul = foldl' (addNullPtrTrans1 nul) cfa (G.labEdges cfa)

addNullPtrTrans1 :: Expr -> CFA -> (Loc,Loc,Statement) -> CFA
addNullPtrTrans1 nul cfa (from , _, SAssign e1 e2) = cfaInsTrans from cfaErrLoc cond cfa
    where cond = SAssume $ disj $ map (=== nul) (exprPtrSubexpr e1 ++ exprPtrSubexpr e2)
    
addNullPtrTrans1 _   cfa (_    , _, SAssume _)     = cfa
