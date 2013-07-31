{-# LANGUAGE ImplicitParams, ScopedTypeVariables, RecordWildCards #-}

module TSLAbsGame(tslAbsGame, 
                  bexprToFormula, 
                  tslUpdateAbsVarAST) where

import Prelude hiding (and)
import Data.List hiding (and)
import Debug.Trace
import Data.Maybe
import Text.PrettyPrint.Leijen.Text
import Data.Text.Lazy hiding (intercalate, map, take, length, zip, filter)
import qualified Data.Graph.Inductive as G

import TSLUtil
import Util hiding (trace)
import qualified CuddExplicitDeref as C
import ISpec
import TranSpec
import IExpr hiding (disj)
import CFA
import Predicate
import Inline
import PID
import qualified Interface   as Abs
import qualified TermiteGame as Abs
import qualified HAST.HAST   as H
import qualified HAST.BDD    as H
import ACFA
import ACFACompile
import BFormula

-----------------------------------------------------------------------
-- Interface
-----------------------------------------------------------------------

tslAbsGame :: Spec -> C.STDdManager s u -> Bool -> Abs.Abstractor s u AbsVar AbsVar
tslAbsGame spec m dofair = Abs.Abstractor { Abs.goalAbs   = tslGoalAbs   spec m
                                          , Abs.fairAbs   = tslFairAbs   spec m
                                          , Abs.initAbs   = tslInitAbs   spec m
                                          , Abs.contAbs   = tslContAbs   spec m
                                          --, gameConsistent  = tslGameConsistent  spec
                                          , Abs.updateAbs = tslUpdateAbs spec m dofair
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

tslConstraint :: (?spec::Spec, ?pred::[Predicate]) => TAST f e c
tslConstraint = H.Disj 
                $ mapIdx (\tr i -> tranPrecondition ("pre_" ++ show i) tr) 
                $ (tsUTran $ specTran ?spec) ++ (tsCTran $ specTran ?spec)

tslUpdateAbs :: Spec -> C.STDdManager s u -> Bool -> [(AbsVar,[C.DDNode s u])] -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslUpdateAbs spec m dofair avars ops = do
    trace ("tslUpdateAbs " ++ (intercalate "," $ map (show . fst) avars)) $ return ()
    let ?ops    = ops
    p <- pdbPred
    let ?spec   = spec
        ?m      = m
        ?pred   = p
        ?dofair = dofair
    mapM tslUpdateAbsVar avars

tslUpdateAbsVar :: (?dofair::Bool, ?ops::PVarOps pdb s u, ?spec::Spec, ?m::C.STDdManager s u, ?pred::[Predicate]) => (AbsVar,[C.DDNode s u]) -> PDB pdb s u (C.DDNode s u)
tslUpdateAbsVar (av, n) = trace ("compiling " ++ show av)
                          $ H.compileBDD ?m ?ops $ tslUpdateAbsVarAST (av,n)


tslUpdateAbsVarAST :: (?dofair::Bool, ?spec::Spec, ?pred::[Predicate]) => (AbsVar, f) -> TAST f e c

-- handle $cont variable in a special way:
-- $cont is false under controllable transition, 
-- $cont can only be true after uncontrollable transition if we are inside a magic block.
tslUpdateAbsVarAST (av, n) | (show av) == mkContVarName && ?dofair = tslConstraint `H.And`
                                                                     (x `H.Imp` (H.Not x')) `H.And` 
                                                                     (x' `H.Imp` magic) `H.And` 
                                                                     (((H.Not x) `H.And` magic) `H.Imp` (x' `H.XNor` lcont))
                           | (show av) == mkContVarName && (not ?dofair) = tslConstraint `H.And`
                                                                           (x `H.Imp` (H.Not x')) `H.And` 
                                                                           (x' `H.Imp` magic) `H.And` 
                                                                           (((H.Not x) `H.And` magic) `H.Imp` ((x' `H.XNor` lcont) `H.And` x')) `H.And`
                                                                           ((H.Not magic) `H.Imp` notidle)
    where 
    x  = H.Var $ H.NVar $ avarBAVar av 
    x' = H.Var $ H.FVar n
    lcont = compileFormula $ ptrFreeBExprToFormula mkContLVar
    magic = compileFormula $ ptrFreeBExprToFormula mkMagicVar
    notidle = H.Not $ H.EqConst (H.NVar $ avarBAVar $ AVarEnum $ TVar mkEPIDLVarName) (enumToInt $ mkEPIDEnumeratorName $ EPIDProc $ PrID "_idle_" [])

tslUpdateAbsVarAST (av, n) | (show av) == mkEPIDVarName = (cont `H.And` eqcont) `H.Or` ((H.Not cont) `H.And` eqlepid)
    where 
    eqcont  = H.EqConst (H.FVar n) (enumToInt $ mkEPIDEnumeratorName EPIDCont)
    eqlepid = H.EqVar   (H.FVar n) (H.NVar $ avarBAVar $ AVarEnum $ TVar mkEPIDLVarName)
    cont = compileFormula $ ptrFreeBExprToFormula mkContVar
    
tslUpdateAbsVarAST (av, n)                              = H.Disj (unchanged:upds)
    where
    trans = mapIdx (\tr i -> varUpdateTrans (show i) [(av,n)] tr) $ (tsUTran $ specTran ?spec) ++ (tsCTran $ specTran ?spec)
    (upds, pres) = unzip $ catMaybes trans
    -- generate condition when variable value does not change
    ident = H.EqVar (H.NVar $ avarBAVar av) (H.FVar n)
    unchanged = H.And (H.Conj $ map H.Not pres) ident
    
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

-- Compute precondition of transition without taking prefix blocks and wires into account
tranPrecondition :: (?spec::Spec, ?pred::[Predicate]) => String -> Transition -> TAST f e c
tranPrecondition trname tran = varUpdateLoc trname [] (tranFrom tran) (tranCFA tran)

-- Compute update functions for a list of variables wrt to a transition
-- Returns update function and precondition of the transition.  The precondition
-- can be used to generate complementary condition when variable value remains 
-- unchanged.  
varUpdateTrans :: (?spec::Spec, ?pred::[Predicate]) => String -> [(AbsVar,f)] -> Transition -> Maybe (TAST f e c, TAST f e c)
varUpdateTrans trname vs Transition{..} = if G.isEmpty cfa
                                             then Nothing
                                             else Just (varUpdateLoc trname vs tranFrom cfa, varUpdateLoc (trname ++ "_pre") [] tranFrom cfa)
    where cfa' = pruneCFAVar (map fst vs) tranCFA
          cfa  = cfaLocInlineWirePrefix ?spec cfa' tranFrom


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
