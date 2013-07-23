{-# LANGUAGE ImplicitParams #-}

module EqSMT(eqTheorySolver) where

import Data.List
import qualified Data.Set as S

import qualified DecisionProcedure as DP
import qualified Var               as DP
import qualified DNFTypes          as DP
import qualified PLit              as DP
import qualified SyntaxTree2       as DP
import qualified SymTab            as DP
import qualified Term              as DP

--import LogicClasses
import Util
import qualified CuddExplicitDeref as C
import Ops
import ISpec
import IVar
import IType
import IExpr
import EUF
import Predicate
import BFormula
import ACFACompile
import RefineCommon
import qualified HAST.BDD  as H

--eqSolver :: Spec -> Solver Predicate s u
--eqSolver spec = TheorySolver { checkSat  = eqCheckSat  spec
--                             , unsatCore = eqUnsatCore spec
--                             --, equant    = eqEquant    spec
--                             }

eqTheorySolver :: Spec -> C.STDdManager s u -> TheorySolver s u AbsVar AbsVar
eqTheorySolver spec m = TheorySolver { unsatCoreState      = eqUnsatCore           spec
                                     , unsatCoreStateLabel = eqUnsatCoreStateLabel spec
                                     , eQuant              = eqEquantTmp           spec m
                                     }


--predVars :: Spec -> Predicate -> [(String, VarCategory)]
--predVars spec (PAtom _ t1 t2) = let ?spec = spec
--                                in S.toList $ S.fromList $ map (\v -> (varName v, varCat v)) $ termVar t1 ++ termVar t2

eqCheckSat :: Spec -> [(AbsVar,[Bool])] -> Maybe Bool
eqCheckSat spec ps = 
    let ?spec = spec
    in if DP.dpSAT (DP.dpContext::EUF) (DP.DNF [map mkALit ps])
          then Just True
          else Just False

eqUnsatCore :: Spec -> [(AbsVar,[Bool])] -> Maybe [(AbsVar,[Bool])]
eqUnsatCore spec ps = 
    let res = eqCheckSat spec ps
        core = foldl' (\pset p -> if eqCheckSat spec (S.toList $ S.delete p pset) == Just False
                                     then S.delete p pset
                                     else pset)
                      (S.fromList ps) ps
    in if res == Just False
          then Just (S.toList core)
          else Nothing

eqEquant :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> [(AbsVar,[Bool])] -> [String] -> PDB pdb s u (C.DDNode s u)
eqEquant spec m ops avs vs = do
    let ?spec = spec
        ?m    = m
        ?ops  = ops
    let dnf0 = DP.DNF [map mkALit avs]
        vs'  = S.toList $ S.fromList vs
        qvs  = map mkVar vs'
        dnf  = {-trace ("eqEquant " ++ show dnf0 ++ " qvars: " ++ show qvs) $-} DP.dpEQuantVars (DP.dpContext::EUF) dnf0 qvs
    --trace ("dnf = " ++ show dnf) $ return ()
    H.compileBDD m ops (compileFormula $ dnfToForm dnf)

   

eqEquantTmp :: Spec -> C.STDdManager s u -> [(AbsVar,[Bool])] -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
eqEquantTmp spec m avs ops = 
    let ?spec = spec
    in eqEquant spec m ops avs
       $ S.toList $ S.fromList 
       $ map varName
       $ filter ((== VarTmp) . varCat) 
       $ concatMap (avarVar . fst) avs
    
eqUnsatCoreStateLabel :: Spec -> [(AbsVar, [Bool])] -> [(AbsVar, [Bool])] -> Maybe ([(AbsVar, [Bool])], [(AbsVar, [Bool])])
eqUnsatCoreStateLabel spec sps lps = 
    let ?spec = spec
    in case eqUnsatCore spec (lps++sps) of
            Just core -> Just $ partition ((==VarState) . avarCategory . fst) core
            _         -> Nothing

mkALit :: (?spec::Spec) => (AbsVar,[Bool]) -> DP.PLit
mkALit (AVarPred (PAtom op t1 t2), [val]) = DP.PLit (mkOp op val) (mkTerm $ ptermTerm t1) (mkTerm $ ptermTerm t2)
mkALit (AVarBool t               , [val]) = DP.PLit DP.Eq         (mkTerm t)  (DP.TLit (boolArrToBitsBe [val]) 1)
mkALit (AVarInt  t               , val)   = DP.PLit DP.Eq         (mkTerm t)  (DP.TLit (boolArrToBitsBe val) (length val))
mkALit (AVarEnum t               , val)   = DP.PLit DP.Eq         (mkTerm t)  (DP.TLit (boolArrToBitsBe val) (length val))

mkOp :: PredOp -> Bool -> DP.BinOpTyp
mkOp PEq  True  = DP.Eq
mkOp PEq  False = DP.Neq
mkOp op   _     = error $ "EqSMT.mkOp: " ++ show op ++ " is not supported"

mkTerm :: (?spec::Spec) => Term -> DP.Term
mkTerm     (TVar n)                = DP.TVar $ mkVar n
mkTerm     (TSInt w i)             = DP.TLit i w
mkTerm     (TUInt w i)             = DP.TLit i w
mkTerm   x@(TField t f)            = case mkTerm t of
                                          DP.TVar (DP.Var p t' c) -> DP.TVar $ DP.Var (p++[(f,Nothing)]) t' c
                                          _                        -> error $ "EqSMT.mkTerm " ++ show x
mkTerm     (TSlice t s)            = DP.TSlice s $ mkTerm t
mkTerm   t@(TBinOp ABConcat t1 t2) = DP.TFunc (DP.FBuiltin DP.FConcat) [mkTerm t1, mkTerm t2] (termWidth t)
mkTerm   t                         = error $ "EqSMT.mkTerm " ++ show t

mkVar :: (?spec::Spec) => String -> DP.Var
mkVar n = {-trace ("mkVar " ++ n ++ ", type " ++ show t) -} DP.Var [(varName v,Nothing)] t DP.VarState
    where v = getVar n
          t = mkType $ varType v

mkType :: (?spec::Spec) => Type -> DP.TypeDef
mkType (UInt w)    = DP.Int w
mkType (Struct fs) = DP.Struct $ map (\(Field n t) -> DP.Named n (mkType t)) fs
mkType (Enum n)    = DP.Enum $ zip (enumEnums $ getEnumeration n) $ map Just [0..]
mkType Bool        = DP.Bool
mkType t           = error $ "EqSMT.mkType " ++ show t

dnfToForm :: (?spec::Spec) => DP.DNF -> Formula
dnfToForm (DP.DNF dnf) = fdisj $ map (fconj . map plitToFormula) dnf

plitToFormula :: (?spec::Spec) => DP.PLit -> Formula
plitToFormula (DP.PLit op t1 t2) = fRel (opToRelOp op) (dpTermToExpr t1) (dpTermToExpr t2)

opToRelOp :: DP.BinOpTyp -> RelOp
opToRelOp DP.Eq  = REq
opToRelOp DP.Neq = RNeq

dpTermToExpr :: (?spec::Spec) => DP.Term -> Expr
dpTermToExpr (DP.TVar (DP.Var [(n,Nothing)] _ _))          = EVar n
dpTermToExpr (DP.TVar (DP.Var ns            t c))          = EField (dpTermToExpr $ DP.TVar $ DP.Var (init ns) t c) (fst $ last ns)
dpTermToExpr (DP.TLit i w)                                 = EConst $ UIntVal w i
dpTermToExpr (DP.TSlice s t)                               = ESlice (dpTermToExpr t) s
dpTermToExpr (DP.TFunc (DP.FBuiltin DP.FConcat) [t1,t2] _) = EBinOp BConcat (dpTermToExpr t1) (dpTermToExpr t2)
dpTermToExpr (DP.TFunc (DP.FBuiltin DP.FConcat) (t1:ts) w) = EBinOp BConcat (dpTermToExpr t1) (dpTermToExpr $ DP.TFunc (DP.FBuiltin DP.FConcat) ts (w - DP.tWidth t1))
