{-# LANGUAGE ImplicitParams, RecordWildCards, TemplateHaskell #-}

module CodeGen() where

import Data.List
import Data.Tuple.Select
import qualified Data.Map          as M
import Control.Lens
import Control.Monad.State
import Control.Monad.ST

import Interface
import BddRecord
import ISpec
import Predicate
import TranSpec
import TSLAbsGame
import GroupTag
import ACFA2HAST
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
---- Annotate pause locations with sets of states
---- Assumes that pause locations that represent magic blocks do not have outgoing transitions.
--cfaAnnotateReachable :: CFA -> DDNode s u -> M.Map Loc DDNode
--cfaAnnotateReachable =
--    where 
--    -- decompose into transitions
--    states = I.cfaDelayLocs cfa
--    tcfas = concatMap (cfaLocTrans cfa) states
--    trans = map (\tcfa -> let from = head $ I.cfaSource tcfa
--                              to   = head $ I.cfaSink tcfa
--                          in I.Transition from to tcfa) tcfas
--
--    -- compile transitions
--    -- fix point computation

-- State maintained when compiling a transition.
-- _cnv collects new untracked predicates to be quantified away after compilation.
data CompileState s u sp lp = CompileState {
    _cnv :: NewVars s u sp,
    _cdb :: DB s u sp lp
}
makeLenses ''CompileState

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


compileTransition :: (?spec::Spec, ?m::C.STDdManager s u) => DB s u AbsVar AbsVar -> Transition -> ST s (DDNode s u)
compileTransition db@DB{_symbolTable = SymbolInfo{..}, _sections = SectionInfo{..}, ..} t = do
    let ops = constructOps ?m
    let ?ops = compileOps ops
    let svars = map (\(av, (_, _, d', _)) -> (av, d'))
                $ filter (\(_, (_, is, _, _)) -> not $ null $ intersect is _trackedInds) 
                $ M.toList _stateVars
    (upd, CompileState _ newvars) <- (flip runStateT) (CompileState M.empty db) $ do
          p <- pdbPred
          let ?pred = p
          let ast = H.Conj $ map (varUpdateTrans t) $ svars
          H.compileBDD ?m ?ops (avarGroupTag . bavarAVar) ast
    cube <- nodesToCube ops $ concat $ M.elems newvars
    upd' <- bexists ops cube upd
    deref ops upd
    deref ops cube
    return upd'
    

allocTmpUntracked :: Ops s u -> sp -> Int -> Maybe String -> StateT (CompileState s u sp lp) (ST s) [DDNode s u]
allocTmpUntracked ops var size group = do
    CompileState{..} <- get
    case M.lookup var _cnv of
         Just nodes -> return nodes
         Nothing    -> do (nodes, _) <- liftToCompileState $ allocN ops size group
                          put $ CompileState (M.insert var nodes _cnv) _cdb
                          return nodes

compileOps :: Ord sp => Ops s u -> VarOps (CompileState s u sp lp) (BAVar sp lp) s u
compileOps ops = VarOps {withTmp = withTmpCompile' ops, allVars = liftToCompileState allVars', ..}
    where
    getVar (StateVar var size) group = do
        SymbolInfo{..} <- use $ db . symbolTable
        findWithDefaultM sel1 var _stateVars (allocTmpUntracked ops var size group)
    getVar  _ _ = error "Requested non-state variable when compiling controllable CFA"


compileTransitionVar :: Transition -> (AbsVar, f) -> TAST f e c
compileTransitionVar t (av, n) = maybe (H.EqVar (H.NVar $ avarBAVar av) (H.FVar n))
                                       fst 
                                       (varUpdateTrans (show av) (av,n) t)
