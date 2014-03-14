{-# LANGUAGE ImplicitParams, RecordWildCards, TemplateHaskell #-}

module CodeGen() where

import Data.List
import Data.Tuple.Select
import qualified Data.Map          as M
import Control.Monad.State
import Control.Monad.ST

import Interface
import BddRecord
import ISpec hiding (getVar)
import Predicate
import TranSpec
import TSLAbsGame
import GroupTag
import ACFA2HAST
import CFA
import qualified CuddExplicitDeref as C
import qualified HAST.HAST         as H
import qualified HAST.BDD          as H

---- code generator interface
--data CodeGen = CodeGen {
--    Pos ->
--}
--
--
--
--

adamsFunction = undefined

simulateCFAAbstract :: Spec -> C.STDdManager s u -> DB s u AbsVar AbsVar -> CFA -> DDNode s u -> Loc -> ST s (Maybe (DDNode s u))
simulateCFAAbstract spec m pdb cfa initset loc = do
    let ?m    = m
        ?spec = spec
        ?db   = pdb
    let Ops{..} = constructOps ?m
    annot <- cfaAnnotateReachable cfa initset
    res <- maybe (return Nothing)
                 (\rel -> do ref rel
                             return $ Just rel)
                 (M.lookup loc annot)
    mapM_ deref $ M.elems annot
    return res


-- Annotate pause locations with sets of states
-- initset - set of possible initial states
-- Assumes that pause locations that represent magic blocks do not have outgoing transitions.
cfaAnnotateReachable :: (?spec::Spec, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) => CFA -> DDNode s u -> ST s (M.Map Loc (DDNode s u))
cfaAnnotateReachable cfa initset = do
    let Ops{..} = constructOps ?m
    -- decompose into transitions
    let states = cfaDelayLocs cfa
        tcfas = concatMap (cfaLocTrans cfa) states
    -- compile transitions
    tupds <- mapM (\(to, tcfa) -> do let from = head $ cfaSource tcfa
                                         sink = head $ cfaSink   tcfa
                                     upd <- compileTransition (Transition from sink tcfa)
                                     if isMBLabel $ cfaLocLabel from cfa
                                        then error "cfaAnnotateReachable: outgoing transition from magic block"
                                        else return (from, to, upd))
                  tcfas
    res <- annotate' tupds [cfaInitLoc] (M.singleton cfaInitLoc initset) 
    mapM_ (deref . sel3) tupds
    return res

annotate' :: (?spec::Spec, ?m::C.STDdManager s u, ?db :: DB s u AbsVar AbsVar)
          => [(Loc, Loc, DDNode s u)]    -- Compiled transitions
          -> [Loc]                               -- Frontier
          -> M.Map Loc (DDNode s u)      -- Annotations computed so far
          -> ST s (M.Map Loc (DDNode s u))
annotate' _    []          annot = return annot
annotate' upds (loc:front) annot = do
    let Ops{..} = constructOps ?m
    -- transitions from loc
    (front'', annot'') <- foldM (\(front', annot') (_, to, upd) -> do 
                                   nxt <- adamsFunction (annot M.! loc) upd
                                   -- If new reachable state have been discovered in to, 
                                   -- annotate to with these states and add it to the frontier
                                   case M.lookup to annot of
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
    let svars = map (\(av, (_, _, d', _)) -> (av, d'))
                $ filter (\(_, (_, is, _, _)) -> not $ null $ intersect is _trackedInds) 
                $ M.toList _stateVars
    (upd, CompileState newvars _) <- (flip runStateT) (CompileState (NewVars []) ?db) $ do
          p <- pdbPred
          let ?pred = p
          let ast = H.Conj $ map (compileTransitionVar t) $ svars
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

compileOps :: Ord sp => Ops s u -> VarOps (CompileState s u sp lp) (BAVar sp lp) s u
compileOps ops = VarOps {withTmp = withTmpCompile' ops, allVars = liftToCompileState allVars', ..}
    where
    getVar (StateVar var size) grp = do
        SymbolInfo{..} <- gets (_symbolTable . _cdb)
        findWithDefaultM sel1 var _stateVars (allocTmpUntracked ops var size grp)
    getVar  _ _ = error "Requested non-state variable when compiling controllable CFA"


compileTransitionVar :: (?spec::Spec, ?pred::[Predicate]) => Transition -> (AbsVar, f) -> TAST f e c
compileTransitionVar t (av, n) = maybe (H.EqVar (H.NVar $ avarBAVar av) (H.FVar n)) fst 
                                       (varUpdateTrans (show av) (av,n) t)
