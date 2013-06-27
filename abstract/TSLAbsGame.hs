{-# LANGUAGE ImplicitParams #-}

module TSLAbsGame(tslAbsGame,
                  bexprToFormula) where

import Prelude hiding (and)
import Data.List hiding (and)
import Debug.Trace

import qualified CuddExplicitDeref as C
import ISpec
import TranSpec
import IExpr hiding (disj)
import CFA
import Predicate
import Inline
import qualified Interface   as Abs
import qualified TermiteGame as Abs
import qualified HAST.HAST   as H
import qualified HAST.BDD    as H
import ACFA
import ACFACompile

-----------------------------------------------------------------------
-- Interface
-----------------------------------------------------------------------

tslAbsGame :: Spec -> C.STDdManager s u -> Abs.Abstractor s u AbsVar AbsVar
tslAbsGame spec m = Abs.Abstractor { Abs.goalAbs   = tslGoalAbs   spec m
                                   , Abs.fairAbs   = tslFairAbs   spec m
                                   , Abs.initAbs   = tslInitAbs   spec m
                                   , Abs.contAbs   = tslContAbs   spec m
                                   --, gameConsistent  = tslGameConsistent  spec
                                   , Abs.updateAbs = tslUpdateAbs spec m
                                   }

tslGoalAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslGoalAbs spec m ops = do
    let ?ops  = ops
    p <- pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    mapM (\g -> do let ast = tranPrecondition (goalCond g)
                   H.compileBDD m ops ast)
         $ tsGoal $ specTran spec

tslFairAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslFairAbs spec m ops = do
    let ?ops  = ops
    p <- pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    mapM (H.compileBDD m ops . bexprAbstract . fairCond) $ tsFair $ specTran spec

tslInitAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslInitAbs spec m ops = do 
    let ?ops  = ops
    p <- pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    let pre   = tranPrecondition (fst $ tsInit $ specTran spec)
        extra = bexprAbstract (snd $ tsInit $ specTran spec)
        res   = H.And pre extra
    H.compileBDD m ops res

-- TODO: where should this go?

--tslGameConsistent :: Spec -> C.STDdManager s u -> PDB s u (C.DDNode s u)
--tslGameConsistent spec m = do
--    let ?m = m
--    -- Enum vars can take values between 0 and n-1 (where n is the size of the enumeration)
--    evars  <- pdbGetEnumVars
--    constr <- mapM (\(av,sz) -> do v <- pdbGetVar av
--                                   constrs <- lift $ mapM (C.eqConst m v) [0..sz-1]
--                                   res <- lift $ C.disj m constrs
--                                   lift $ mapM (C.deref m) constrs
--                                   return res) 
--                   $ M.toList evars
--    res <- lift $ C.conj m constr
--    lift $ mapM (C.deref m) constr
--    return res

tslContAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslContAbs spec m ops = do 
    let ?ops  = ops
    p <- pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    H.compileBDD m ops $ bexprAbstract $ mkContVar === true

tslUpdateAbs :: Spec -> C.STDdManager s u -> [(AbsVar,[C.DDNode s u])] -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslUpdateAbs spec m avars ops = do
    trace ("tslUpdateAbs " ++ (intercalate "," $ map (show . fst) avars)) $ return ()
    let ?ops  = ops
    p <- pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    let pervar = map (\av -> let cont  = varUpdateTrans [av] $ tsCTran $ specTran spec
                                 ucont = H.Disj $ map (varUpdateTrans [av]) $ tsUTran $ specTran spec
                             in H.Or cont ucont)
                        avars
    mapM (H.compileBDD m ops) pervar

----------------------------------------------------------------------------
-- PDB operations
----------------------------------------------------------------------------

pdbPred :: (?ops::PVarOps pdb s u) => PDB pdb s u [Predicate]
pdbPred = do
    bavars <- Abs.allVars ?ops
    return $ map (\(AVarPred p) -> p)
           $ filter avarIsPred 
           $ map bavarAVar bavars

----------------------------------------------------------------------------
-- Predicate/variable update functions
----------------------------------------------------------------------------

bexprAbstract :: (?spec::Spec, ?pred::[Predicate]) => Expr -> TAST f e c
bexprAbstract = compileFormula . bexprToFormula

-- Compute precondition of transition without taking always blocks and wires into account
tranPrecondition :: (?spec::Spec, ?pred::[Predicate]) => Transition -> TAST f e c
tranPrecondition tran = varUpdateLoc [] (tranFrom tran) (tranCFA tran)

-- Compute update functions for a list of variables wrt to a transition
varUpdateTrans :: (?spec::Spec, ?pred::[Predicate]) => [(AbsVar,f)] -> Transition -> TAST f e c
varUpdateTrans vs tran = varUpdateLoc vs (tranFrom tran) (cfaLocInlineWireAlways ?spec (tranCFA tran) (tranFrom tran))

-- Compute update functions for a list of variables for a location inside
-- transition CFA. 
varUpdateLoc :: (?spec::Spec, ?pred::[Predicate]) => [(AbsVar, f)] -> Loc -> CFA -> TAST f e c
varUpdateLoc vs loc cfa = compileACFA vs $ tranCFAToACFA (map fst vs) loc cfa
