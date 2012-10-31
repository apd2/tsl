{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module CFA(Statement(..),
           (=:),
           nop,
           Loc,
           LocLabel(..),
           CFA,
           isDelayLabel,
           newCFA,
           cfaErrLoc,
           cfaErrVarName,
           cfaInitLoc,
           cfaInsLoc,
           cfaLocLabel,
           cfaInsTrans,
           cfaInsTransMany,
           cfaInsTrans',
           cfaInsTransMany',
           cfaErrTrans,
           cfaSuc,
           cfaAddNullPtrTrans,
           cfaPruneUnreachable,
           cfaTrace,
           cfaTraceFile,
           cfaShow,
           cfaSave) where

import qualified Data.Graph.Inductive.Graph    as G
import qualified Data.Graph.Inductive.Tree     as G
import qualified Data.Graph.Inductive.Graphviz as G
import Data.List
import Data.Tuple
import Text.PrettyPrint
import System.IO.Unsafe
import System.Process
import Data.String.Utils
import Debug.Trace

import PP
import Util hiding (name,trace)
import IExpr


-- Atomic statement
data Statement = SAssume Expr
               | SAssign Expr Expr

instance PP Statement where
    pp (SAssume e)   = text "assume" <+> (parens $ pp e)
    pp (SAssign l r) = pp l <+> text ":=" <+> pp r

instance Show Statement where
    show = render . pp

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

instance PP LocLabel where
    pp LNone      = empty
    pp (LPause e) = pp e
    pp LFinal     = text "F"

instance Show LocLabel where
    show = render . pp

instance PP CFA where
    pp cfa = text "states:"
             $+$
             (vcat $ map (\(loc,lab) -> pp loc <> char ':' <+> pp lab) $ G.labNodes cfa)
             $+$
             text "transitions:"
             $+$
             (vcat $ map (\(from,to,s) -> pp from <+> text "-->" <+> pp to <> char ':' <+> pp s) $ G.labEdges cfa)

instance Show CFA where
    show = render . pp

cfaTrace :: CFA -> String -> a -> a
cfaTrace cfa title x = unsafePerformIO $ do
    cfaShow cfa title
    return x

cfaTraceFile :: CFA -> String -> a -> a
cfaTraceFile cfa title x = unsafePerformIO $ do
    cfaSave cfa title
    return x

cfaShow :: CFA -> String -> IO ()
cfaShow cfa title = do
    fname <- cfaSave cfa title
    readProcess "evince" [fname] ""
    return ()

cfaSave :: CFA -> String -> IO String
cfaSave cfa title = do
    let -- Convert graph to dot format
        title' = replace "\"" "_" $ replace "/" "_" title
        fname = "cfa_" ++ title' ++ ".ps"
        graphstr = G.graphviz cfa title' (6.0, 11.0) (1,1) G.Portrait
    writeFile (fname++".dot") graphstr
    readProcess "dot" ["-Tps", "-o" ++ fname] graphstr 
    return fname


isDelayLabel :: LocLabel -> Bool
isDelayLabel (LPause _) = True
isDelayLabel LFinal     = True
isDelayLabel LNone      = False

newCFA :: Expr -> CFA 
newCFA initcond = G.insNode (cfaInitLoc,LPause initcond) $ G.insNode (cfaErrLoc,(LPause false)) G.empty

cfaErrLoc :: Loc
cfaErrLoc = 0

cfaErrVarName :: String
cfaErrVarName = "$err"

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
cfaInsTransMany from to [] cfa = cfaInsTrans from to nop cfa
cfaInsTransMany from to stats cfa = cfaInsTrans aft to (last stats) cfa'
    where (cfa', aft) = foldl' (\(cfa, loc) stat -> let (cfa',loc') = cfaInsLoc LNone cfa
                                                    in (cfaInsTrans loc loc' stat cfa', loc'))
                               (cfa, from) (init stats)

cfaInsTrans' :: Loc -> Statement -> CFA -> (CFA, Loc)
cfaInsTrans' from stat cfa = (cfaInsTrans from to stat cfa', to)
    where (cfa', to) = cfaInsLoc LNone cfa

cfaInsTransMany' :: Loc -> [Statement] -> CFA -> (CFA, Loc)
cfaInsTransMany' from stats cfa = (cfaInsTransMany from to stats cfa', to)
    where (cfa', to) = cfaInsLoc LNone cfa

cfaErrTrans :: Loc -> Statement -> CFA -> CFA
cfaErrTrans loc stat cfa =
    let (cfa',loc') = cfaInsTrans' loc stat cfa
    in cfaInsTrans loc' cfaErrLoc (EVar cfaErrVarName =: true) cfa'

cfaSuc :: Loc -> CFA -> [(Statement,Loc)]
cfaSuc loc cfa = map swap $ G.lsuc cfa loc

-- Add error transitions for all potential null-pointer dereferences
cfaAddNullPtrTrans :: CFA -> Expr -> CFA
cfaAddNullPtrTrans cfa nul = foldl' (addNullPtrTrans1 nul) cfa (G.labEdges cfa)

addNullPtrTrans1 :: Expr -> CFA -> (Loc,Loc,Statement) -> CFA
addNullPtrTrans1 nul cfa (from , _, SAssign e1 e2) = case cond of
                                                          EConst (BoolVal False) -> cfa
                                                          _ -> cfaErrTrans from (SAssume cond) cfa
    where cond = disj $ map (=== nul) (exprPtrSubexpr e1 ++ exprPtrSubexpr e2)
    
addNullPtrTrans1 _   cfa (_    , _, SAssume _)     = cfa


cfaPruneUnreachable :: CFA -> [Loc] -> CFA
cfaPruneUnreachable cfa keep = 
    let unreach = filter (\n -> (not $ elem n ([cfaInitLoc, cfaErrLoc] ++ keep)) && (null $ G.pre cfa n)) $ G.nodes cfa
    in if null unreach 
          then cfa   
          else trace ("cfaPruneUnreachable: " ++ show cfa ++ "\n"++ show unreach) $
               cfaPruneUnreachable (foldl' (\cfa n -> G.delNode n cfa) cfa unreach) keep


