{-# LANGUAGE ImplicitParams #-}

module EqSMT(eqSolver) where

import Data.List
import qualified Data.Set as S

import qualified DecisionProcedure as DP
import qualified Var               as DP
import qualified DNFTypes          as DP
import qualified PLit              as DP
import qualified Term              as DP
import qualified SyntaxTree2       as DP
import qualified SymTab            as DP

--import LogicClasses
import qualified CuddExplicitDeref as C
import ISpec
import IVar
import IType
import EUF
import Predicate
import PredicateDB
import FCompile
import BFormula
import Solver

eqSolver :: Spec -> Solver Predicate s u
eqSolver spec = Solver { checkSat  = eqCheckSat  spec
                       , unsatCore = eqUnsatCore spec
                       , equant    = eqEquant    spec
                       , predVars  = eqPredVars  spec}

eqPredVars :: Spec -> Predicate -> [(String, VarCategory)]
eqPredVars spec (PAtom _ t1 t2) = let ?spec = spec
                                  in map (\v -> (varName v, varCat v)) $ termVar t1 ++ termVar t2

eqCheckSat :: Spec -> [(Predicate,Bool)] -> SatResult
eqCheckSat spec ps = 
    let ?spec = spec
    in if DP.dpSAT (DP.dpContext::EUF) (DP.DNF [map mkPLit ps])
          then SatYes
          else SatNo

eqUnsatCore :: Spec -> [(Predicate,Bool)] -> (SatResult, [(Predicate,Bool)])
eqUnsatCore spec ps = 
    let res = eqCheckSat spec ps
        core = foldl' (\pset p -> if eqCheckSat spec (S.toList $ S.delete p pset) == SatNo
                                            then S.delete p pset
                                            else pset)
                      (S.fromList ps) ps
    in if res == SatNo
          then (res, S.toList core)
          else (res, [])

eqEquant :: Spec -> [(Predicate,Bool)] -> [String] -> PDB s u (C.DDNode s u)
eqEquant spec ps vs = do
    let ?spec = spec
    let dnf = DP.dpEQuantVars (DP.dpContext::EUF) (DP.DNF [map mkPLit ps]) (map mkVar vs)
    compileFormula $ dnfToForm dnf

mkPLit :: (?spec::Spec) => (Predicate,Bool) -> DP.PLit
mkPLit (PAtom op t1 t2, pol) = DP.PLit (mkOp op pol) (mkTerm t1) (mkTerm t2)

mkOp :: RelOp -> Bool -> DP.BinOpTyp
mkOp REq  True  = DP.Eq
mkOp REq  False = DP.Neq
mkOp RNeq True  = DP.Neq
mkOp RNeq False = DP.Eq
mkOp op   _     = error $ "EqSMT.mkOp: " ++ show op ++ " is not supported"

mkTerm :: (?spec::Spec) => Term -> DP.Term
mkTerm   (TVar n)                = DP.TVar $ mkVar n
mkTerm   (TSInt w i)             = DP.TLit i w
mkTerm   (TUInt w i)             = DP.TLit i w
mkTerm x@(TField t f)            = case mkTerm t of
                                        DP.TVar (DP.Var p typ c) -> DP.TVar $ DP.Var (p++[(f,Nothing)]) typ c
                                        _                        -> error $ "EqSMT.mkTerm " ++ show x
mkTerm   (TSlice t s)            = DP.TSlice s $ mkTerm t
mkTerm   t                       = error $ "EqSMT.mkTerm " ++ show t

mkVar :: (?spec::Spec) => String -> DP.Var
mkVar n = DP.Var [(varName v,Nothing)] (mkType $ varType v) DP.VarState
    where v = getVar n

mkType :: (?spec::Spec) => Type -> DP.TypeDef
mkType (UInt w)    = DP.Int w
mkType (Struct fs) = DP.Struct $ map (\(Field n t) -> DP.Named n (mkType t)) fs
mkType t           = error $ "EqSMT.mkType " ++ show t

dnfToForm :: (?spec::Spec) => DP.DNF -> Formula
dnfToForm (DP.DNF dnf) = fdisj $ map (fconj . map plitToPred) dnf

plitToPred :: (?spec::Spec) => DP.PLit -> Formula
plitToPred (DP.PLit op t1 t2) = fAtom (opToRelOp op) (dptermToTerm t1) (dpTermToTerm t2)

opToRelOp :: DP.BinOpTyp -> RelOp
opToRelOp DP.Eq  = REq
opToRelOp DP.Neq = RNeq

dptermToTerm :: (?spec::Spec) => DP.Term -> Term
dptermToTerm (DP.TVar (DP.Var [(n,Nothing)] _ _)) = TVar n
dptermToTerm (DP.TVar (DP.Var ns            t c)) = TField (dpTermToTerm $ DP.TVar $ DP.Var (init ns) t c) (fst $ last ns)
dpTermToTerm (DP.TLit i w)                        = TUInt w i
dpTermToTerm (DP.TSlice s t)                      = TSlice (dpTermToTerm t) s
