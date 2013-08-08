module EqSMTSimple(Var,
                   Pred(..),
                   checkSat,
                   unsatCore,
                   eQuant) where 

import Data.List
import qualified Data.Set as S

import Util
import qualified DecisionProcedure as DP
import qualified Var               as DP
import qualified VarSlice          as DP
import qualified DNFTypes          as DP
import qualified PLit              as DP
import qualified SyntaxTree2       as DP
import qualified SymTab            as DP
import qualified Term              as DP
import EUF

type Var = (String, Int, (Int, Int))
data Pred = EqPred Var Var
          | EqConst Var Int
          deriving (Eq,Ord)

checkSat :: [(Pred, Bool)] -> Bool
checkSat ps = DP.dpSAT (DP.dpContext::EUF) (DP.DNF [map mkLit ps])

mkLit :: (Pred,Bool) -> DP.PLit
mkLit (EqPred  v1 v2          , b) = DP.PLit (if' b DP.Eq DP.Neq) (mkTerm v1) (mkTerm v2)
mkLit (EqConst v@(_,_,(l,h)) i, b) = DP.PLit (if' b DP.Eq DP.Neq) (mkTerm v)  (DP.TLit (fromIntegral i) (h-l+1))

mkVS :: Var -> DP.VarSlice
mkVS (n,w,(l,h)) = (DP.Var [(n,Nothing)] (DP.Int w) DP.VarState, (l,h))

mkTerm :: Var -> DP.Term
mkTerm v = DP.TSlice s' (DP.TVar v') where (v',s') = mkVS v

unsatCore :: [(Pred, Bool)] -> Maybe [(Pred, Bool)]
unsatCore ps = if' res Nothing (Just (S.toList core))
    where
    res = checkSat ps
    core = foldl' (\pset p -> if' (checkSat (S.toList $ S.delete p pset)) pset (S.delete p pset))
                  (S.fromList ps) ps
    
eQuant :: [Var] -> [(Pred, Bool)] -> [[(Pred, Bool)]]
eQuant vs ps = map (map plitToPred) dnf
    where
    dnf0 = DP.DNF [map mkLit ps]
    qvs  = map mkVS vs
    DP.DNF dnf  = {-trace ("eqEquant " ++ show dnf0 ++ " qvars: " ++ show qvs) $-} DP.dpEQuant (DP.dpContext::EUF) dnf0 qvs

plitToPred :: DP.PLit -> (Pred, Bool)
plitToPred (DP.PLit DP.Eq  t1 t2) = (mkPred t1 t2, True)
plitToPred (DP.PLit DP.Neq t1 t2) = (mkPred t1 t2, False)

mkPred :: DP.Term -> DP.Term -> Pred
mkPred (DP.TLit i w) t2            = EqConst (dpTermToVar t2) (fromInteger i)
mkPred t1            (DP.TLit i w) = EqConst (dpTermToVar t1) (fromInteger i)
mkPred t1            t2            = EqPred  (dpTermToVar t1) (dpTermToVar t2)

dpTermToVar (DP.TVar v@(DP.Var [(n,Nothing)] _ _))               = (n, DP.vWidth v, (0, DP.vWidth v-1))
dpTermToVar (DP.TSlice s (DP.TVar v@(DP.Var [(n,Nothing)] _ _))) = (n, DP.vWidth v, s)
