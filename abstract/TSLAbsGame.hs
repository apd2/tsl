{-# LANGUAGE ImplicitParams, ScopedTypeVariables #-}

module TSLAbsGame(tslAbsGame,
                  bexprToFormula) where

import Prelude hiding (and)
import Data.List hiding (and)
import Debug.Trace
import Text.PrettyPrint.Leijen.Text
import Data.Text.Lazy hiding (intercalate, map, take, length, zip, filter)

import TSLUtil
import Util hiding (trace)
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
    mapM (\g -> do let ast = tranPrecondition ("goal_" ++ (goalName g))  (goalCond g)
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
    let pre   = tranPrecondition "init" (fst $ tsInit $ specTran spec)
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
    let pervar = map (\av -> let cont  = varUpdateTrans "cont" [av] $ tsCTran $ specTran spec
                                 ucont = H.Disj $ mapIdx (\tr i -> varUpdateTrans (show i) [av] tr) $ tsUTran $ specTran spec
                             in H.Or cont ucont)
                     avars
    _ <- mapIdxM (\tr i -> cfaTraceFile (tranCFA tr) ("cfa" ++ show i) $ return ()) $ tsUTran $ specTran spec
    mapM (\(ast, (av,_)) -> trace ("compiling " ++ show av) $ H.compileBDD m ops ast) $ zip pervar avars

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
tranPrecondition :: (?spec::Spec, ?pred::[Predicate]) => String -> Transition -> TAST f e c
tranPrecondition trname tran = varUpdateLoc trname [] (tranFrom tran) (tranCFA tran)

-- Compute update functions for a list of variables wrt to a transition
varUpdateTrans :: (?spec::Spec, ?pred::[Predicate]) => String -> [(AbsVar,f)] -> Transition -> TAST f e c
varUpdateTrans trname vs tran = varUpdateLoc trname vs (tranFrom tran) (cfaLocInlineWireAlways ?spec (tranCFA tran) (tranFrom tran))

-- Compute update functions for a list of variables for a location inside
-- transition CFA. 
varUpdateLoc :: (?spec::Spec, ?pred::[Predicate]) => String -> [(AbsVar, f)] -> Loc -> CFA -> TAST f e c
varUpdateLoc trname vs loc cfa = acfaTraceFile acfa ("acfa_" ++ trname ++ "_" ++ vlst)
                                 $ traceFile ("HAST for " ++ vlst ++ ":\n" ++ show ast') (trname ++ "-" ++ vlst ++ ".ast") ast
    where
    acfa = tranCFAToACFA (map fst vs) loc cfa
    ast  = compileACFA vs acfa
    vs'  = map (\(av,_) -> (av, text $ pack $ show av ++ "'")) vs
    vlst = intercalate "_" $ map (show . snd) vs'
    ast'::(TAST Doc Doc Doc) = compileACFA vs' acfa
