{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module CFA(Statement(..),
           Frame(..),
           frameMethod,
           Stack,
           (=:),
           Loc,
           LocAction(..),
           LocLabel(..),
           TranLabel(..),
           CFA,
           isDelayLabel,
           newCFA,
           cfaErrLoc,
           cfaErrVarName,
           cfaInitLoc,
           cfaDelayLocs,
           cfaInsLoc,
           cfaLocLabel,
           cfaLocSetAct,
           cfaLocSetStack,
           cfaInsTrans,
           cfaInsTransMany,
           cfaInsTrans',
           cfaInsTransMany',
           cfaErrTrans,
           cfaSuc,
           cfaFinal,
           cfaAddNullPtrTrans,
           cfaPruneUnreachable,
           cfaTrace,
           cfaTraceFile,
           cfaTraceFileMany,
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

import Name
import PP
import Util hiding (name,trace)
import NS
import IExpr

-- Frontend imports
import qualified Statement as F
import qualified Expr      as F
import qualified Method    as F

-- Atomic statement
data Statement = SAssume Expr
               | SAssign Expr Expr
               deriving (Eq)

instance PP Statement where
    pp (SAssume e)   = text "assume" <+> (parens $ pp e)
    pp (SAssign l r) = pp l <+> text ":=" <+> pp r

instance Show Statement where
    show = render . pp

(=:) :: Expr -> Expr -> Statement
(=:) e1 e2 = SAssign e1 e2

------------------------------------------------------------
-- Control-flow automaton
------------------------------------------------------------

type Loc = G.Node

-- Syntactic element associated with CFA location
data LocAction = ActStat F.Statement
               | ActExpr F.Expr
               | ActNone

-- Stack frame
data Frame = Frame {
    fScope :: Scope,
    fLoc   :: Loc
}

frameMethod :: Frame -> Maybe F.Method
frameMethod f = case fScope f of
                     ScopeMethod _ m -> Just m
                     _               -> Nothing

type Stack = [Frame]

data LocLabel = LInst  {locAct :: LocAction}
              | LPause {locAct :: LocAction, locStack :: Stack, locExpr :: Expr}
              | LFinal {locAct :: LocAction, locStack :: Stack}

instance PP LocLabel where
    pp (LInst  _)     = empty
    pp (LPause _ _ e) = pp e
    pp (LFinal _ _)   = text "F"

instance Show LocLabel where
    show = render . pp

data TranLabel = TranCall F.Method
               | TranReturn
               | TranNop
               | TranStat Statement

instance Eq TranLabel where
    (==) (TranCall m1) (TranCall m2) = sname m1 == sname m2
    (==) TranReturn    TranReturn    = True
    (==) TranNop       TranNop       = True
    (==) (TranStat s1) (TranStat s2) = s1 == s2
    (==) _             _             =  False

instance PP TranLabel where
    pp (TranCall m)  = text "call" <+> text (sname m)
    pp TranReturn    = text "return"
    pp TranNop       = text ""
    pp (TranStat st) = pp st

instance Show TranLabel where
    show = render . pp

type CFA = G.Gr LocLabel TranLabel

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

sanitize :: String -> String
sanitize title = replace "\"" "_" $ replace "/" "_" $ replace "$" "" $ replace ":" "_" title

cfaTraceFile :: CFA -> String -> a -> a
cfaTraceFile cfa title x = unsafePerformIO $ do
    _ <- cfaSave cfa title False
    return x

cfaTraceFileMany :: [CFA] -> String -> a -> a
cfaTraceFileMany cfas title x = unsafePerformIO $ do
    fnames <- mapM (\(cfa,n) -> cfaSave cfa (title++show n) True) $ zip cfas ([1..]::[Int])
    _ <- readProcess "psmerge" (["-o" ++ (sanitize title) ++ ".ps"]++fnames) ""
    return x

cfaShow :: CFA -> String -> IO ()
cfaShow cfa title = do
    fname <- cfaSave cfa title True
    _ <- readProcess "evince" [fname] ""
    return ()

cfaSave :: CFA -> String -> Bool -> IO String
cfaSave cfa title tmp = do
    let -- Convert graph to dot format
        title' = sanitize title
        fname = (if tmp then "/tmp/" else "") ++ "cfa_" ++ title' ++ ".ps"
        graphstr = cfaToDot cfa title'
    writeFile (fname++".dot") graphstr
    _ <- readProcess "dot" ["-Tps", "-o" ++ fname] graphstr 
    return fname

cfaToDot :: CFA -> String -> String
cfaToDot cfa title = G.graphviz cfa' title (6.0, 11.0) (1,1) G.Portrait
    where cfa' = G.emap (format . show) cfa
          maxLabel = 64
          format :: String -> String
          format s | length s <= maxLabel = s
                   | otherwise            =
                       take maxLabel s ++ "\n" ++ format (drop maxLabel s)

isDelayLabel :: LocLabel -> Bool
isDelayLabel (LPause _ _ _) = True
isDelayLabel (LFinal _ _)   = True
isDelayLabel (LInst _)      = False


newCFA :: Scope -> F.Statement -> Expr -> CFA 
newCFA sc stat initcond = G.insNode (cfaInitLoc,LPause (ActStat stat) [Frame sc cfaInitLoc] initcond) 
                        $ G.insNode (cfaErrLoc,LPause ActNone [Frame sc cfaErrLoc] false) G.empty

cfaErrLoc :: Loc
cfaErrLoc = 0

cfaErrVarName :: String
cfaErrVarName = "$err"

cfaInitLoc :: Loc
cfaInitLoc = 1

cfaDelayLocs :: CFA -> [Loc]
cfaDelayLocs = map fst . filter (isDelayLabel . snd) . G.labNodes

cfaInsLoc :: LocLabel -> CFA -> (CFA, Loc)
cfaInsLoc lab cfa = (G.insNode (loc,lab) cfa, loc)
   where loc = (snd $ G.nodeRange cfa) + 1

cfaLocLabel :: Loc -> CFA -> LocLabel
cfaLocLabel loc cfa = fromJustMsg "cfaLocLabel" $ G.lab cfa loc

cfaLocSetAct :: Loc -> LocAction -> CFA -> CFA
cfaLocSetAct loc act cfa = G.gmap (\(to, lid, n, from) -> 
                                    (to, lid, if lid == loc then n {locAct = act} else n, from)) cfa


cfaLocSetStack :: Loc -> Stack -> CFA -> CFA
cfaLocSetStack loc stack cfa = G.gmap (\(to, lid, n, from) -> 
                                      (to, lid, if lid == loc then n {locStack = stack} else n, from)) cfa


cfaInsTrans :: Loc -> Loc -> TranLabel -> CFA -> CFA
cfaInsTrans from to stat cfa = G.insEdge (from,to,stat) cfa

cfaInsTransMany :: Loc -> Loc -> [TranLabel] -> CFA -> CFA
cfaInsTransMany from to [] cfa = cfaInsTrans from to TranNop cfa
cfaInsTransMany from to stats cfa = cfaInsTrans aft to (last stats) cfa'
    where (cfa', aft) = foldl' (\(_cfa, loc) stat -> cfaInsTrans' loc stat _cfa) 
                               (cfa, from) (init stats)

cfaInsTrans' :: Loc -> TranLabel -> CFA -> (CFA, Loc)
cfaInsTrans' from stat cfa = (cfaInsTrans from to stat cfa', to)
    where (cfa', to) = cfaInsLoc (LInst ActNone) cfa

cfaInsTransMany' :: Loc -> [TranLabel] -> CFA -> (CFA, Loc)
cfaInsTransMany' from stats cfa = (cfaInsTransMany from to stats cfa', to)
    where (cfa', to) = cfaInsLoc (LInst ActNone) cfa

cfaErrTrans :: Loc -> TranLabel -> CFA -> CFA
cfaErrTrans loc stat cfa =
    let (cfa',loc') = cfaInsTrans' loc stat cfa
    in cfaInsTrans loc' cfaErrLoc (TranStat $ EVar cfaErrVarName =: true) cfa'

cfaSuc :: Loc -> CFA -> [(TranLabel,Loc)]
cfaSuc loc cfa = map swap $ G.lsuc cfa loc

cfaFinal :: CFA -> [Loc]
cfaFinal cfa = map fst $ filter (\n -> case snd n of
                                            LFinal _ _ -> True
                                            _          -> False) $ G.labNodes cfa

-- Add error transitions for all potential null-pointer dereferences
cfaAddNullPtrTrans :: CFA -> Expr -> CFA
cfaAddNullPtrTrans cfa nul = foldl' (addNullPtrTrans1 nul) cfa (G.labEdges cfa)

addNullPtrTrans1 :: Expr -> CFA -> (Loc,Loc,TranLabel) -> CFA
addNullPtrTrans1 nul cfa (from , to, l@(TranStat (SAssign e1 e2))) = 
    case cond of
         EConst (BoolVal False) -> cfa
         _ -> let (cfa1, from') = cfaInsLoc (LInst ActNone) cfa
                  cfa2 = cfaInsTrans from' to l $ G.delLEdge (from, to, l) cfa1
                  cfa3 = cfaInsTrans from from' (TranStat $ SAssume $ neg cond) cfa2
              in cfaErrTrans from (TranStat $ SAssume cond) cfa3
    where cond = disj $ map (=== nul) (exprPtrSubexpr e1 ++ exprPtrSubexpr e2)
    
addNullPtrTrans1 _   cfa (_    , _, _)                        = cfa


cfaPruneUnreachable :: CFA -> [Loc] -> CFA
cfaPruneUnreachable cfa keep = 
    let unreach = filter (\n -> (not $ elem n keep) && (null $ G.pre cfa n)) $ G.nodes cfa
    in if null unreach 
          then cfa
          else --trace ("cfaPruneUnreachable: " ++ show cfa ++ "\n"++ show unreach) $
               cfaPruneUnreachable (foldl' (\_cfa n -> G.delNode n _cfa) cfa unreach) keep
