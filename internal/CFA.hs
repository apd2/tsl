{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ImplicitParams #-}

module CFA(Statement(..),
           Frame(..),
           frameMethod,
           Stack,
           (=:),
           Loc,
           LocAction(..),
           isActNone,
           LocLabel(..),
           TranLabel(..),
           CFA,
           isDelayLabel,
           isDeadendLoc,
           newCFA,
           cfaNop,
           cfaErrVarName,
           cfaInitLoc,
           cfaDelayLocs,
           cfaInsLoc,
           cfaLocLabel,
           cfaLocSetAct,
           cfaLocSetStack,
           cfaLocInline,
           cfaLocWaitCond,
           cfaInsTrans,
           cfaInsTransMany,
           cfaInsTrans',
           cfaInsTransMany',
           cfaErrTrans,
           cfaSuc,
           cfaFinal,
           cfaAddNullTypes,
           cfaPruneUnreachable,
           cfaReachInst,
           cfaPrune,
           cfaTrace,
           cfaTraceFile,
           cfaTraceFileMany,
           cfaShow,
           cfaSave) where

import qualified Data.Graph.Inductive as G
import Data.Maybe
import Data.List
import Data.Tuple
import qualified Data.Set             as S
import qualified Data.Map             as M
import Text.PrettyPrint

import Name
import PP
import Ops
import Util hiding (name)
import TSLUtil
import IExpr
import IType
import {-# SOURCE #-} ISpec

-- Frontend imports
import qualified NS        as F
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

isActNone :: LocAction -> Bool
isActNone ActNone = True
isActNone _       = False

instance PP LocAction where
    pp (ActStat s) = pp s
    pp (ActExpr e) = pp e
    pp ActNone     = empty

instance Show LocAction where
    show = render . pp

-- Stack frame
data Frame = Frame { fScope :: F.Scope
                   , fLoc   :: Loc}

instance PP Frame where
    pp (Frame sc loc) =                         text (show sc) <> char ':' <+> pp loc

frameMethod :: Frame -> Maybe F.Method
frameMethod f = case fScope f of
                     F.ScopeMethod _ m -> Just m
                     _                 -> Nothing

type Stack = [Frame]

instance PP Stack where
    pp stack = vcat $ map pp stack

data LocLabel = LInst  {locAct :: LocAction}
              | LPause {locAct :: LocAction, locStack :: Stack, locExpr :: Expr}
              | LFinal {locAct :: LocAction, locStack :: Stack}

instance PP LocLabel where
    pp (LInst  a)     = pp a
    pp (LPause a _ e) = text "wait" <> (parens $ pp e) $$ pp a
    pp (LFinal a _)   = text "F"                       $$ pp a

instance Show LocLabel where
    show = render . pp

data TranLabel = TranCall F.Method (Maybe Loc) -- method and return location
               | TranReturn
               | TranNop
               | TranStat Statement

instance Eq TranLabel where
    (==) (TranCall m1 l1) (TranCall m2 l2) = sname m1 == sname m2 && l1 == l2
    (==) TranReturn       TranReturn       = True
    (==) TranNop          TranNop          = True
    (==) (TranStat s1)    (TranStat s2)    = s1 == s2
    (==) _                _                = False

instance PP TranLabel where
    pp (TranCall m l) = text "call" <+> text (sname m) <+> text "retloc=" <> pp l
    pp TranReturn     = text "return"
    pp TranNop        = text ""
    pp (TranStat st)  = pp st

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
cfaTrace cfa title x = graphTrace cfa title x

cfaTraceFile :: CFA -> String -> a -> a
cfaTraceFile cfa title x = graphTraceFile cfa title x

cfaTraceFileMany :: [CFA] -> String -> a -> a
cfaTraceFileMany cfas title x = graphTraceFileMany cfas title x

cfaShow :: CFA -> String -> IO ()
cfaShow cfa title = graphShow cfa title

cfaSave :: CFA -> String -> Bool -> IO String
cfaSave cfa title tmp = graphSave cfa ("cfa_" ++ title) tmp

isDelayLabel :: LocLabel -> Bool
isDelayLabel (LPause _ _ _) = True
isDelayLabel (LFinal _ _)   = True
isDelayLabel (LInst _)      = False

isDeadendLoc :: CFA -> Loc -> Bool
isDeadendLoc cfa loc = G.outdeg cfa loc == 0

cfaLocWaitCond :: CFA -> Loc -> Expr
cfaLocWaitCond cfa loc = case cfaLocLabel loc cfa of
                              LPause _ _ c -> c
                              LFinal _ _   -> true

newCFA :: F.Scope -> F.Statement -> Expr -> CFA 
newCFA sc stat initcond = G.insNode (cfaInitLoc,LPause (ActStat stat) [Frame sc cfaInitLoc] initcond) G.empty

cfaErrVarName :: String
cfaErrVarName = "$err"

cfaInitLoc :: Loc
cfaInitLoc = 1

cfaNop :: CFA
cfaNop = cfaInsTrans cfaInitLoc fin TranNop cfa
    where (cfa, fin) = cfaInsLoc (LFinal ActNone [])
                       $ G.insNode (cfaInitLoc,LInst ActNone) G.empty

cfaDelayLocs :: CFA -> [Loc]
cfaDelayLocs = map fst . filter (isDelayLabel . snd) . G.labNodes

cfaInsLoc :: LocLabel -> CFA -> (CFA, Loc)
cfaInsLoc lab cfa = (G.insNode (loc,lab) cfa, loc)
   where loc = (snd $ G.nodeRange cfa) + 1

cfaLocLabel :: Loc -> CFA -> LocLabel
cfaLocLabel loc cfa = fromJustMsg "cfaLocLabel" $ G.lab cfa loc

cfaLocSetAct :: Loc -> LocAction -> CFA -> CFA
cfaLocSetAct loc act cfa = graphUpdNode loc (\n -> n {locAct = act}) cfa 
          
cfaLocSetStack :: Loc -> Stack -> CFA -> CFA
cfaLocSetStack loc stack cfa = graphUpdNode loc (\n -> n {locStack = stack}) cfa

cfaLocInline :: CFA -> Loc -> CFA -> CFA
cfaLocInline cfa loc inscfa = inlineBetween cfa2 loc loc' inscfa
    -- Replicate location.  The new location is not a delay location
    -- and contains all outgoing transitions of the original location
    where (cfa1, loc') = cfaInsLoc (LInst $ locAct $ cfaLocLabel loc cfa) cfa
          cfa2 = foldl' (\cfa' (toloc, lab) -> G.delLEdge (loc, toloc, lab) 
                                               $ cfaInsTrans loc' toloc lab cfa')
                        cfa1 (G.lsuc cfa loc)

inlineBetween :: CFA -> Loc -> Loc -> CFA -> CFA
inlineBetween cfa0 bef aft inscfa = 
    let -- for each node in inscfa, create a replica in CFA and store
        -- correspondence in a table
        (cfa1, locs1) = foldl' (\(cfa,locs) loc -> let lab = cfaLocLabel loc inscfa
                                                       (cfa', loc') = cfaInsLoc (LInst $ locAct lab) cfa
                                                   in if' (loc == cfaInitLoc)                     (cfaInsTrans bef loc' TranNop cfa', locs ++ [loc']) $
                                                      if' (isDelayLabel $ cfaLocLabel loc inscfa) (cfa, locs ++ [aft]) $
                                                      (cfa', locs++[loc']))
                               (cfa0,[]) (G.nodes inscfa)
        match = M.fromList $ zip (G.nodes inscfa) locs1
    in -- copy transitions over
       foldl' (\cfa (from, to, l) -> cfaInsTrans (match M.! from) (match M.! to) l cfa) cfa1 (G.labEdges inscfa)

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

cfaErrTrans :: Loc -> Loc -> CFA -> CFA
cfaErrTrans from to cfa = cfaInsTrans from to (TranStat $ EVar cfaErrVarName =: true) cfa

cfaSuc :: Loc -> CFA -> [(TranLabel,Loc)]
cfaSuc loc cfa = map swap $ G.lsuc cfa loc

cfaFinal :: CFA -> [Loc]
cfaFinal cfa = map fst $ filter (\n -> case snd n of
                                            LFinal _ _ -> True
                                            _          -> False) $ G.labNodes cfa

-- Add types to NullVal expressions introduced by cfaAddNullPtrTrans
cfaAddNullTypes :: Spec -> CFA -> CFA
cfaAddNullTypes spec cfa = G.emap (\l -> case l of 
                                              TranStat st -> TranStat $ (statAddNullTypes spec) st
                                              _           -> l) cfa

statAddNullTypes :: Spec -> Statement -> Statement
statAddNullTypes spec (SAssume (EBinOp Eq e (EConst (NullVal _)))) = let ?spec = spec in
                                                                     SAssume (EBinOp Eq e (EConst $ NullVal $ typ e))
statAddNullTypes _    s = s


cfaPruneUnreachable :: CFA -> [Loc] -> CFA
cfaPruneUnreachable cfa keep = 
    let unreach = filter (\n -> (not $ elem n keep) && (null $ G.pre cfa n)) $ G.nodes cfa
    in if null unreach 
          then cfa
          else --trace ("cfaPruneUnreachable: " ++ show cfa ++ "\n"++ show unreach) $
               cfaPruneUnreachable (foldl' (\_cfa n -> G.delNode n _cfa) cfa unreach) keep

-- locations reachable from specified location before reaching the next delay location
-- (the from location if not included in the result)
cfaReachInst :: CFA -> Loc -> S.Set Loc
cfaReachInst cfa from = cfaReachInst' cfa S.empty (S.singleton from)

cfaReachInst' :: CFA -> S.Set Loc -> S.Set Loc -> S.Set Loc
cfaReachInst' cfa found frontier = if S.null frontier'
                                     then found'
                                     else cfaReachInst' cfa found' frontier'
    where new       = suc frontier
          found'    = S.union found new
          -- frontier' - all newly discovered states that are not pause or final states
          frontier' = S.filter (not . isDelayLabel . fromJust . G.lab cfa) $ new S.\\ found
          suc locs  = S.unions $ map suc1 (S.toList locs)
          suc1 loc  = S.fromList $ G.suc cfa loc

-- Prune CFA, leaving only specified subset of locations
cfaPrune :: CFA -> S.Set Loc -> CFA
cfaPrune cfa locs = foldl' (\g l -> if S.member l locs then g else G.delNode l g) cfa (G.nodes cfa)

