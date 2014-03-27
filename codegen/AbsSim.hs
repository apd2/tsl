{-# LANGUAGE ImplicitParams, RecordWildCards, TemplateHaskell #-}

module AbsSim (CompiledMB,
               simulateCFAAbstractToLoc,
               simulateCFAAbstractToCompletion,
               simulateGameAbstract,
               restrictToMB,
               compileExpr) where

import Data.List
import Data.Maybe
import Data.Tuple.Select
import qualified Data.Map          as M
import Control.Monad.State
import Control.Monad.ST

import Util
import PID
import Interface
import TermiteGame
import BddRecord
import BddUtil
import ISpec hiding (getVar)
import Predicate
import TranSpec
import TSLAbsGame
import GroupTag
import ACFA2HAST
import CFA
import Pos
import CG
import Inline
import BFormula
import qualified IExpr             as I
import qualified CuddExplicitDeref as C
import qualified HAST.HAST         as H
import qualified HAST.BDD          as H


----------------------------------------------------------
-- Type
----------------------------------------------------------

type CompiledMB      = (Pos, CFA)
type CompiledMB' s u = (DDNode s u, CFA)

type DbgNotify s u = (String -> DDNode s u -> ST s ())

----------------------------------------------------------
-- Interface
----------------------------------------------------------

-- Generate condition that holds whenever the magic block specified by 
-- mbpos is active.
mbToStateConstraint :: Spec -> C.STDdManager s u -> DB s u AbsVar AbsVar -> Pos -> ST s (DDNode s u)
mbToStateConstraint spec m pdb mbpos = do
    let Ops{..} = constructOps m
    let ?spec = spec
        ?m    = m
        ?db   = pdb
    let mblocs = specLookupMB spec mbpos
    compileExpr $ I.conj [mkMagicVar, I.disj $ map (\(pid, mbloc, _) -> let cfa = specGetCFA spec (EPIDProc pid) 
                                                                        in mkPCEq cfa pid (mkPC pid mbloc)) 
                                               mblocs]

-- Restrict a relation to states inside the MB
restrictToMB :: Spec -> C.STDdManager s u -> DB s u AbsVar AbsVar -> Pos -> DDNode s u -> ST s (DDNode s u)
restrictToMB spec m pdb mbpos set = do
    let Ops{..} = constructOps m
    if set == bfalse
       then traceST "restrictToMB: set is false"
       else traceST "restrictToMB: set is not false"
    cond <- mbToStateConstraint spec m pdb mbpos
    if cond == bfalse
       then traceST "restrictToMB: cond is false"
       else traceST "restrictToMB: cond is not false"
    res <- cond .& set
    if res == bfalse
       then traceST "restrictToMB: res is false"
       else traceST "restrictToMB: res is not false"

    deref cond
    return res

-- Abstractly simulate CFA consisting of controllable transitions from 
-- initial location to the specified pause location.
simulateCFAAbstractToLoc :: Spec -> C.STDdManager s u -> RefineDynamic s u -> DB s u AbsVar AbsVar -> DDNode s u -> Lab s u -> CFA -> DDNode s u -> Loc -> DbgNotify s u -> ST s (Maybe (DDNode s u))
simulateCFAAbstractToLoc spec m refdyn pdb cont lp cfa initset loc cb = do
    let ?m    = m
        ?spec = spec
        ?db   = pdb
        ?rd   = refdyn
        ?cont = cont
        ?lp   = lp
        ?cb   = cb
    let Ops{..} = constructOps ?m
    annot <- cfaAnnotateReachable cfa initset
    res <- maybe (return Nothing)
                 (\rel -> do ref rel
                             return $ Just rel)
                 (M.lookup loc annot)
    mapM_ deref $ M.elems annot
    return res

-- Abstractly simulate controllable CFA to completion.  
-- Return the set of final states.
simulateCFAAbstractToCompletion :: Spec -> C.STDdManager s u -> RefineDynamic s u -> DB s u AbsVar AbsVar -> DDNode s u -> Lab s u -> CFA -> DDNode s u -> DbgNotify s u -> ST s (DDNode s u)
simulateCFAAbstractToCompletion spec m refdyn pdb cont lp cfa initset cb = do
    traceST "simulateCFAAbstractToCompletion"
    let ops = constructOps m
    let ?m    = m
        ?spec = spec
        ?db   = pdb
        ?rd   = refdyn
        ?cont = cont
        ?lp   = lp
        ?cb   = cb
    let Ops{..} = constructOps ?m
    annot <- cfaAnnotateReachable cfa initset
    let finalsets = mapMaybe (\loc -> M.lookup loc annot) $ cfaFinal cfa
    res <- disj ops finalsets
    mapM_ deref $ M.elems annot
    traceST "simulateCFAAbstractToCompletion done"
    return res

-- Simulate the entire game starting from the initial set. Include 
-- completely implemented magic blocks in the simulation.  Returns the set
-- of reachable states.
simulateGameAbstract :: Spec -> C.STDdManager s u -> RefineDynamic s u -> DB s u AbsVar AbsVar -> DDNode s u -> Lab s u -> [CompiledMB] -> DDNode s u -> DbgNotify s u -> ST s (DDNode s u)
simulateGameAbstract spec m refdyn pdb@DB{_symbolTable = SymbolInfo{..}, _sections = SectionInfo{..}, ..} cont lp mbs initset' cb = do
    let Ops{..} = constructOps m
    let ?m    = m
        ?spec = spec
        ?rd   = refdyn
        ?db   = pdb
        ?cont = cont
        ?lp   = lp
        ?cb   = cb
    -- Compute the set of initial states
    let initvs = (concatMap sel1 $ M.elems _initVars) \\ (concatMap sel1 $ M.elems _stateVars)
    initcube <- nodesToCube initvs
    init0 <- bexists initcube initset'
    deref initcube
    initset <- bexists _untrackedCube init0
    deref init0
    -- Compute magic block constraints
    mbs' <- mapM (\(p, cfa) -> do cond <- mbToStateConstraint spec m pdb p
                                  return (cond, cfa)) mbs
    -- Start fix point computation from this set
    res <- simulateGameAbstractFrom mbs' initset
    mapM_ (deref . fst) mbs'
    return res


----------------------------------------------------------
-- Internals
----------------------------------------------------------

-- Simulate the entire game starting from the given set.
simulateGameAbstractFrom ::(?spec::Spec, ?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::DDNode s u, ?lp::Lab s u, ?cb::DbgNotify s u) => [CompiledMB' s u] -> DDNode s u -> ST s (DDNode s u)
simulateGameAbstractFrom mbs initset = do
    let ops@Ops{..} = constructOps ?m
        RefineDynamic{..} = ?rd
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
    -- transitive closure of uncontrollable from initset
    reach <- applyUncontrollableTC ops (SynthData sinfo trans ?cont ?rd ?lp) initset
    traceST "applyUncontrollableTC done"
    -- simulate magic blocks
    deltas <- mapM (\(cond, cfa) -> do bef <- cond .& reach
                                       aft <- simulateCFAAbstractToCompletion ?spec ?m ?rd ?db ?cont ?lp cfa bef ?cb
                                       deref bef
                                       aft' <- clearMagic aft
                                       deref aft
                                       return aft')
                   mbs
    traceST "deltas done"
    -- add new sets
    reach' <- disj ops $ reach:deltas
    mapM_ deref $ reach:deltas
    done <- leq reach' initset
    deref initset
    -- repeat unless fixed point reached
    if done
       then return reach'
       else simulateGameAbstractFrom mbs reach'

-- Takes a set of states and forces the magic variable to false.
clearMagic :: (?spec::Spec, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> ST s (DDNode s u)
clearMagic set = do
    let Ops{..} = constructOps ?m
        DB{_symbolTable = SymbolInfo{..}, ..} = ?db
    magcube <- nodesToCube $ sel1 $ _stateVars M.! (AVarBool $ TVar mkMagicVarName)
    set' <- bexists magcube set
    deref magcube
    nmagic <- compileExpr $ I.neg mkMagicVar
    res <- band set' nmagic
    deref nmagic
    deref set'
    return res

compileExpr :: (?spec::Spec, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) => I.Expr -> ST s (DDNode s u)
compileExpr e = 
    (flip evalStateT) (CompileState (NewVars []) ?db) 
     $ H.compileBDD ?m (compileOps $ constructOps ?m) (avarGroupTag . bavarAVar) 
     $ compileFormula 
     $ ptrFreeBExprToFormula e

-- Simulate a controllable transition tr from "from" followed by a transitive 
-- closure of uncontrollable transitions.
-- Assumes that label variables and don't cares in tr.
simulateControllable :: (?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::DDNode s u, ?lp::Lab s u) => DDNode s u -> DDNode s u -> ST s (DDNode s u)
simulateControllable from tr = do
    -- E x, u, l . tr & from & c+c
    let ops@Ops{..} = constructOps ?m
        RefineDynamic{..} = ?rd
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
    trfrom  <- tr .& from
    trfromc0 <- trfrom .& consistentPlusCULCont
    deref trfrom
    trfromc1 <- bexists _trackedCube trfromc0
    deref trfromc0
    trfromc2 <- bexists _untrackedCube trfromc1
    deref trfromc1
    trfromc3 <- bexists _outcomeCube trfromc2
    deref trfromc2
    to' <- bexists _labelCube trfromc3
    deref trfromc3
    to <- shift _nextNodes _trackedNodes to'
    deref to'
    totc <- applyUncontrollableTC ops (SynthData sinfo trans ?cont ?rd ?lp) to
    deref to
    return totc


-- Annotate pause locations with sets of states
-- initset - set of possible initial states
-- Assumes that pause locations that represent magic blocks do not have outgoing transitions.
cfaAnnotateReachable :: (?spec::Spec, ?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::DDNode s u, ?lp::Lab s u, ?cb::DbgNotify s u) => CFA -> DDNode s u -> ST s (M.Map Loc (DDNode s u))
cfaAnnotateReachable cfa initset = do
    let Ops{..} = constructOps ?m
    ref initset
    -- decompose into transitions; ignore transitions from MBs
    let states = filter (not . isMBLoc cfa) {-$ cfaTraceFile cfa "cfaAnnotateReachable"-} $ cfaDelayLocs cfa
        tcfas = concatMap (cfaLocTrans cfa) states
    -- compile transitions
    tupds <- mapM (\(to, tcfa) -> do let from = head $ cfaSource tcfa
                                         sink = head $ cfaSink   tcfa
                                     upd <- compileTransition (Transition from sink tcfa)
                                     ?cb ("from" ++ show from ++ "to" ++ show to) upd
                                     return (from, to, upd))
                  tcfas
    res <- annotate' tupds [cfaInitLoc] (M.singleton cfaInitLoc initset) 
    mapM_ (deref . sel3) tupds
    return res

annotate' :: (?spec::Spec, ?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db :: DB s u AbsVar AbsVar, ?cont::DDNode s u, ?lp::Lab s u)
          => [(Loc, Loc, DDNode s u)]    -- Compiled transitions
          -> [Loc]                       -- Frontier
          -> M.Map Loc (DDNode s u)      -- Annotations computed so far
          -> ST s (M.Map Loc (DDNode s u))
annotate' _    []          annot = return annot
annotate' upds (loc:front) annot = do
    let Ops{..} = constructOps ?m
    -- transitions from loc
    (front'', annot'') <- foldM (\(front', annot') (_, to, upd) -> do 
                                   nxt <- simulateControllable (annot' M.! loc) upd
                                   -- If new reachable states have been discovered in to, 
                                   -- annotate to with these states and add it to the frontier
                                   case M.lookup to annot' of
                                      Nothing  -> return (to:front', M.insert to nxt annot')
                                      Just ann -> do issubset <- leq nxt ann
                                                     if issubset
                                                        then do deref nxt
                                                                return (front', annot')
                                                        else do newannot <- nxt .| ann
                                                                deref nxt
                                                                deref ann
                                                                return (to:front', M.insert to newannot annot'))
                          (front, annot)
                          $ filter ((== loc) . sel1) upds
    annotate' upds front'' annot''

-- State maintained when compiling a transition.
-- _cnv collects new untracked predicates to be quantified away after compilation.
data CompileState s u sp lp = CompileState {
    _cnv :: NewVars s u sp,
    _cdb :: DB s u sp lp
}
--makeLenses ''CompileState

liftToCompileState :: StateT (DB s u sp lp) (ST s) a -> StateT (CompileState s u sp lp) (ST s) a
liftToCompileState (StateT func) = StateT $ \st -> do
    (res, st') <- func (_cdb st) 
    return (res, CompileState (_cnv st) st')

withTmpCompile' :: Ops s u -> (DDNode s u -> StateT (CompileState s u sp lp) (ST s) a) -> StateT (CompileState s u sp lp) (ST s) a
withTmpCompile' Ops{..} func = do
    ind <- liftToCompileState allocIdx
    var <- lift $ ithVar ind
    res <- func var
    liftToCompileState $ freeIdx ind
    lift $ deref var
    return res


compileTransition :: (?db::DB s u AbsVar AbsVar, ?spec::Spec, ?m::C.STDdManager s u) => Transition -> ST s (DDNode s u)
compileTransition t = do
    let DB{_symbolTable = SymbolInfo{..}, _sections = SectionInfo{..}, ..} = ?db
    let ops@Ops{..} = constructOps ?m
    let ?ops = compileOps ops
    let trname = ("from" ++ show (tranFrom t) ++ "to" ++ show (tranTo t))
    let svars = map (\(av, (_, _, d', _)) -> (av, d'))
                $ filter (\(_, (_, is, _, _)) -> not $ null $ intersect is _trackedInds) 
                $ M.toList _stateVars
    (upd, CompileState newvars _) <- (flip runStateT) (CompileState (NewVars []) ?db) $ do
          p <- pdbPred
          let ?pred = p
          let pre = tranPrecondition trname t
              ast = H.Conj $ pre : (map (compileTransitionVar t) $ svars)
          H.compileBDD ?m ?ops (avarGroupTag . bavarAVar) ast
    cube <- nodesToCube $ concatMap snd $ _allocatedStateVars newvars
    upd' <- bexists cube upd
    deref upd
    deref cube
    return upd'
    

allocTmpUntracked :: (Ord sp) => Ops s u -> sp -> Int -> Maybe String -> StateT (CompileState s u sp lp) (ST s) [DDNode s u]
allocTmpUntracked ops var size grp = do
    CompileState{..} <- get
    case lookup var $ _allocatedStateVars _cnv of
         Just nodes -> return nodes
         Nothing    -> do (nodes, _) <- liftToCompileState $ allocN ops size grp
                          put $ CompileState (NewVars $ (var, nodes) : _allocatedStateVars _cnv) _cdb
                          return nodes

compileOps :: (Ord sp, Ord lp, Show lp) => Ops s u -> VarOps (CompileState s u sp lp) (BAVar sp lp) s u
compileOps ops = VarOps {withTmp = withTmpCompile' ops, allVars = liftToCompileState allVars', ..}
    where
    getVar (StateVar var size) grp = do
        SymbolInfo{..} <- gets (_symbolTable . _cdb)
        findWithDefaultM sel1 var _stateVars (allocTmpUntracked ops var size grp)
    getVar (LabelVar var _)    _ = do
        SymbolInfo{..} <- gets (_symbolTable . _cdb)
        findWithDefaultM sel1 var _labelVars (error $ "Requested unknown label variable " ++ show var ++ " when compiling controllable CFA")

compileTransitionVar :: (?spec::Spec, ?pred::[Predicate]) => Transition -> (AbsVar, f) -> TAST f e c
compileTransitionVar t (av, n) = maybe ident
                                       (\(upd, pre) -> let unchanged = H.And (H.Not pre) ident
                                                       in H.Or upd unchanged)
                                       (varUpdateTrans (show av) (av,n) t)
    where ident = H.EqVar (H.NVar $ avarBAVar av) (H.FVar n)
