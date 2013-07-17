{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards, ScopedTypeVariables #-}

-- Convert flattened spec to internal representation
module SpecInline (spec2Internal) where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State hiding (guard)
import qualified Data.Graph.Inductive.Graph as G

import TSLUtil
import Util hiding (name, trace)
import Spec
import qualified ISpec    as I
import qualified TranSpec as I
import qualified IExpr    as I
import qualified CFA      as I
import qualified IType    as I
import qualified IVar     as I
import PID
import Pos
import Name
import NS
import Statement
import StatementInline
import Expr
import ExprInline
import Template
import TemplateFlatten
import TVar
import Method
import Process
import Type
import Inline
import SMTSolver

-- Main function
spec2Internal :: (?solver::SMTSolver) => Spec -> I.Spec
spec2Internal s = 
    let -- preprocessing
        ?spec = specSimplify s in
    let cfas = I.specAllCFAs spec
        epids = nub $ map (cid2epid . fst) cfas
        -- PC variables and associated enums
        (pcvars, pcenums) = unzip 
                            $ map (\(cid,cfa) -> let enum = I.Enumeration (mkPCEnumName cid) $ map (mkPCEnum cid) $ I.cfaDelayLocs cfa
                                                     var  = I.Var False I.VarState (mkPCVarName cid) (I.Enum $ I.enumName enum)
                                                 in (var, enum)) $ filter ((/= CCID) . fst) cfas
        -- built-in enums used in translating choice{} statements
        choiceenum = map mkChoiceEnumDecl [0..9]
        senum = mapMaybe (\d -> case tspec d of
                                     EnumSpec _ es -> Just $ I.Enumeration (sname d) (map sname es)
                                     _             -> Nothing) (specType ?spec)                                                     
        (pidvar, pidenum)  = mkEPIDVarDecl epids
        (vars, tagenum)    = mkVars
 
        ((specWire, specAlways, inittran, goals), (_, extratmvars)) = 
            runState (do wire      <- mkWires
                         always    <- mkAlways
                         inittr    <- mkInit
                         usergoals <- mapM mkGoal $ tmGoal tmMain
                         maggoal   <- mkMagicGoal
                         return (wire, always, inittr, if' (not $ null usergoals) usergoals [maggoal]))
                     (0,[])
        extraivars = let ?scope = ScopeTemplate tmMain in map (\v -> mkVarDecl (varMem v) (NSID Nothing Nothing) v) extratmvars
        (specProc, tmppvs) = unzip $ (map procToCProc $ tmProcess tmMain) 
        (specCTask,tmpcvs) = unzip
                             $ map (\m -> let (cfa, vs) = let ?procs = [] in taskToCFA Nothing m
                                          in (I.Task m cfa, vs))
                             $ filter ((== Task Controllable) . methCat)
                             $ tmMethod tmMain
        specEnum           = choiceenum ++ (pidenum : tagenum : (senum ++ pcenums))
        specVar            = cvars ++ [pidvar, mkEPIDLVarDecl] ++ pcvars ++ vars ++ concat (tmppvs ++ tmpcvs) ++ extraivars
        specCAct           = ctran
        specTran           = error "specTran undefined"
        spec               = I.Spec {..}
        spec'              = I.specMapCFA (I.cfaAddNullTypes spec) spec

        -- Controllable transitions
        (ctran, cvars) = mkCTran 
        -- Uncontrollable transitions
        utran = concatMap (\(cid, cfa) -> cfaToITransitions cid cfa) 
                          $ filter ((/= CCID) . fst)
                          $ I.specAllCFAs spec'
        -- initialise PC variables.
        pcinit = map (\cid -> mkPCVar cid I.=== mkPC cid I.cfaInitLoc) 
                 $ filter (/= CCID) 
                 $ map fst $ I.specAllCFAs spec'
        -- initialise $en vars to false
        teninit = concatMap (mapPTreeTask (\pid m -> mkEnVar pid (Just m) I.=== I.false)) $ tmProcess tmMain
        peninit = concatMap (mapPTreeFProc (\pid _ -> mkEnVar pid Nothing  I.=== I.false)) $ tmProcess tmMain
        -- Initialise $tag, $magic, $cont
        taginit  = mkTagVar   I.=== tagIdle
        maginit  = mkMagicVar I.=== I.false
        continit = mkContVar  I.=== I.false
        --pidinit  = mkPIDVar   I.=== mkPIDEnum pidIdle
        errinit  = mkErrVar   I.=== I.false in

        spec' {I.specTran = I.TranSpec { I.tsCTran  = cfaToITransition ctran "ctran"
                                       , I.tsUTran  = utran
                                       , I.tsWire   = cfaToITransition (fromMaybe I.cfaNop (I.specWire spec'))   "wires"
                                       , I.tsAlways = cfaToITransition (fromMaybe I.cfaNop (I.specAlways spec')) "always"
                                       , I.tsInit   = (inittran, I.conj $ (pcinit ++ teninit ++ peninit ++ [errinit, taginit, maginit, continit{-, pidinit-}]))
                                       , I.tsGoal   = goals
                                       , I.tsFair   = mkFair spec'
                                       }}


------------------------------------------------------------------------------
-- Preprocess all statements and expressions before inlining.  
-- In the preprocessed spec:
-- * Method calls can only appear in top-level expressions
-- * No method calls in return statements
-- * Local variables are declared and initialised separately
------------------------------------------------------------------------------

specSimplify :: Spec -> Spec
specSimplify s = let ?spec = s
                 in s{specTemplate = [tmSimplify (head $ specTemplate s)]}

tmSimplify :: (?spec::Spec) => Template -> Template
tmSimplify tm = tm { tmProcess = map (procSimplify tm) (tmProcess tm)
                   , tmMethod  = map (methSimplify tm) (tmMethod tm)}

procSimplify :: (?spec::Spec) => Template -> Process -> Process
procSimplify tm p = let ?scope = ScopeProcess tm p
                    in p { procStatement = evalState (statSimplify $ procStatement p) (0,[])}

methSimplify :: (?spec::Spec) => Template -> Method -> Method
methSimplify tm m = let ?scope = ScopeMethod tm m
                    in m { methBody = Right $ evalState (statSimplify $ fromRight $ methBody m) (0,[])}

----------------------------------------------------------------------
-- Wires
----------------------------------------------------------------------

-- Generate transition that assigns all wire variables.  It will be
-- implicitly prepended to all "regular" transitions.
mkWires :: (?spec::Spec, ?solver::SMTSolver) => NameGen (Maybe I.CFA)
mkWires | (null $ tmWire tmMain) = return Nothing
        | otherwise              = do
    let wires = orderWires
        -- Generate assignment statement for each wire
    stat <- let ?scope = ScopeTemplate tmMain
            in statSimplify $ SSeq nopos $ map (\w -> SAssign (pos w) (ETerm nopos [name w]) (fromJust $ wireRHS w)) wires
    let ctx = CFACtx { ctxCID     = Nothing
                     , ctxStack   = [(ScopeTemplate tmMain, error "return from a wire assignment", Nothing, M.empty)]
                     , ctxCFA     = I.newCFA (ScopeTemplate tmMain) stat I.true
                     , ctxBrkLocs = [error "break outside a loop"]
                     , ctxGNMap   = globalNMap
                     , ctxLastVar = 0
                     , ctxVar     = []}
        ctx' = let ?procs =[] in execState (do aft <- procStatToCFA stat I.cfaInitLoc
                                               ctxPause aft I.true I.ActNone) ctx
    return $ Just $ I.cfaTraceFile (ctxCFA ctx') "wires_cfa" $ ctxCFA ctx'


-- Build total order of wires so that for each wire, all wires that
-- it depends on occur eaerlier in the ordering. 
-- Recursively prune nodes without dependencies from the wire dependency graph.
-- (assumes that the graph is acyclic)
orderWires :: (?spec::Spec) => [Wire]
orderWires = map (\n -> getWire s $ fromJust $ G.lab g n) $ orderWires' g
    where s = ScopeTemplate tmMain
          g = wireGraph

orderWires' :: (?spec::Spec) => WireGraph -> [G.Node]
orderWires' g | G.noNodes g == 0  = []
              | otherwise         = ord ++ orderWires' g'
    where (g',ord) = foldl' (\(g0,ord0) n -> if null $ G.suc g0 n then (G.delNode n g0, ord0++[n]) else (g0,ord0))
                            (g,[]) (G.nodes g)

----------------------------------------------------------------------
-- Always-block
----------------------------------------------------------------------

-- Generate transition that performs all always-actions.  It will be
-- implicitly prepended to all "regular" transitions.
mkAlways :: (?spec::Spec, ?solver::SMTSolver) => NameGen (Maybe I.CFA)
mkAlways | (null $ tmAlways tmMain) = return Nothing
         | otherwise                = do
    stat <- let ?scope = ScopeTemplate tmMain
            in statSimplify $ SSeq nopos $ map alwBody $ tmAlways tmMain
    let ctx = CFACtx { ctxCID     = Nothing
                     , ctxStack   = [(ScopeTemplate tmMain, error "return from an always-block", Nothing, M.empty)]
                     , ctxCFA     = I.newCFA (ScopeTemplate tmMain) stat I.true
                     , ctxBrkLocs = [error "break outside a loop"]
                     , ctxGNMap   = globalNMap
                     , ctxLastVar = 0
                     , ctxVar     = []}
        ctx' = let ?procs =[] in execState (do aft <- procStatToCFA stat I.cfaInitLoc
                                               ctxPause aft I.true I.ActNone) ctx
    return $ Just $ I.cfaTraceFile (ctxCFA ctx') "always_cfa" $ ctxCFA ctx'

----------------------------------------------------------------------
-- Fair sets
----------------------------------------------------------------------

mkFair :: (?spec::Spec) => I.Spec -> [I.FairRegion]
mkFair ispec = mkFairSched : mkFairCont ++ (map mkFairProc $ I.specAllProcs ispec)
    where 
    -- Fair scheduling:  GF (not ($magic==true && $cont == false))
    mkFairSched = I.FairRegion "fair_scheduler" $ (mkMagicVar I.=== I.true) `I.land` (mkContVar I.=== I.false)

    mkFairCont | null (I.specCTask ispec) = []
               | otherwise                = [I.FairRegion "fair_cont" $ I.disj $ map (\t -> mkFairCFA (I.taskCFA t) (CTCID $ I.taskMethod t)) $ I.specCTask ispec]

    -- For each uncontrollable process: 
    -- GF (not ((\/i . pc=si && condi) && lastpid /= pid))
    -- where si and condi are process pause locations and matching conditions
    -- i.e, the process eventually either becomes disabled or makes a transition.
    mkFairProc :: (PrID, I.Process) -> I.FairRegion
    mkFairProc (pid,p) = I.FairRegion ("fair_" ++ show pid)
                         $ I.disj 
                         $ mkFairCFA (I.procCFA p) (UCID pid Nothing) : map (\t -> mkFairCFA (I.taskCFA t) (UCID pid (Just $ I.taskMethod t))) (I.procTask p)

    mkFairCFA :: I.CFA -> CID -> I.Expr
    mkFairCFA cfa cid = 
        (mkEPIDVar I./== mkEPIDEnum (cid2epid cid)) `I.land`
        (I.disj $ map (\loc -> (mkPCVar cid I.=== mkPC cid loc) `I.land` (I.cfaLocWaitCond cfa loc)) 
                $ filter (not . I.isDeadendLoc cfa) 
                $ I.cfaDelayLocs cfa)

----------------------------------------------------------------------
-- Init and goal conditions
----------------------------------------------------------------------

mkInit :: (?spec::Spec, ?solver::SMTSolver) => NameGen I.Transition
mkInit = do 
    -- conjunction of initial variable assignments
    let ass = SSeq nopos
              $ mapMaybe (\v -> case varInit $ gvarVar v of
                                     Nothing -> Nothing
                                     Just e  -> Just $ SAssume (pos v) $ EBinOp (pos v) Eq (ETerm nopos $ [name v]) e) (tmVar tmMain)
        -- add init blocks
        cond = SAssume nopos $ eAnd nopos $ map initBody (tmInit tmMain)
    mkCond "$init" (SSeq nopos [ass, cond]) []

-- $err == false
noerror :: I.Expr
noerror = I.EUnOp Not mkErrVar

mkGoal :: (?spec::Spec, ?solver::SMTSolver) => Goal -> NameGen I.Goal
mkGoal g = -- Add $err==false to the goal condition
           (liftM $ I.Goal (sname g)) $ mkCond (sname g) (SAssume nopos $ goalCond g) [I.EUnOp Not mkMagicVar, noerror]

-- In addition to regular goals, we are required to be outside a magic block
-- infinitely often
mkMagicGoal :: (?spec::Spec, ?solver::SMTSolver) => NameGen I.Goal
mkMagicGoal = (liftM $ I.Goal "$magic_goal") $ mkCond "$magic_goal" (SAssume nopos $ EBool nopos True) [I.EUnOp Not mkMagicVar, noerror]

mkCond :: (?spec::Spec, ?solver::SMTSolver) => String -> Statement -> [I.Expr] -> NameGen I.Transition
mkCond descr s extra = do
    -- simplify and convert into a statement
    stat <- let ?scope = ScopeTemplate tmMain 
            in statSimplify s
    let ctx = CFACtx { ctxCID     = Nothing
                     , ctxStack   = [(ScopeTemplate tmMain, error $ "return from " ++ descr, Nothing, M.empty)]
                     , ctxCFA     = I.newCFA (ScopeTemplate tmMain) stat I.true
                     , ctxBrkLocs = error "break outside a loop"
                     , ctxGNMap   = globalNMap
                     , ctxLastVar = 0
                     , ctxVar     = []}
        ctx' = let ?procs =[] in execState (do aft <- procStatToCFA stat I.cfaInitLoc
                                               ctxPause aft I.true I.ActNone) ctx
        trans = locTrans (ctxCFA ctx') I.cfaInitLoc
        -- precondition
    return $ case trans of
                  [t] -> let res = foldl' tranAppend t (map I.SAssume extra)
                         in I.cfaTraceFile (I.tranCFA res) descr $ res
                  _   -> error $ "mkCond " ++ show s ++ ": Invalid condition"

----------------------------------------------------------------------
-- Idle transition
----------------------------------------------------------------------

--mkIdleProc :: (?spec::Spec) => Process
--mkIdleProc = Process nopos (Ident nopos procNameIdle) (SForever nopos $ SPause nopos)

----------------------------------------------------------------------
-- Controllable transitions
----------------------------------------------------------------------

-- only allow controllable transitions when inside a magic block and in
-- a controllable state
contGuard = I.SAssume $ I.conj $ [mkMagicVar I.=== I.true, mkContVar I.=== I.true]

-- generate CFA that represents all possible controllable transitions
mkCTran :: (?spec::Spec, ?solver::SMTSolver) => (I.CFA, [I.Var])
mkCTran = I.cfaTraceFile (ctxCFA ctx' ) "cont_cfa" $ (ctxCFA ctx', ctxVar ctx')
    where sc   = ScopeTemplate tmMain
          stat = SChoice nopos 
                 $ SMagExit nopos : 
                   (map (\m -> SInvoke nopos (MethodRef nopos [name m]) 
                               $ replicate (length $ methArg m) (ENonDet nopos))
                    $ filter ((== Task Controllable) . methCat) $ tmMethod tmMain)
          stat' = let ?scope = sc in evalState (statSimplify stat) (0,[])
          ctx  = CFACtx { ctxCID     = Just CCID
                        , ctxStack   = [(sc, error "return from controllable transition", Nothing, M.empty)]
                        , ctxCFA     = I.newCFA sc (SSeq nopos []) I.true
                        , ctxBrkLocs = []
                        , ctxGNMap   = globalNMap
                        , ctxLastVar = 0
                        , ctxVar     = []}
          ctx' = let ?procs = [] in execState (do aftguard <- ctxInsTrans' I.cfaInitLoc (I.TranStat contGuard)
                                                  aftcall  <- procStatToCFA stat' aftguard
                                                  ctxFinal aftcall) ctx

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------

mkVars :: (?spec::Spec) => ([I.Var], I.Enumeration)
mkVars = (mkErrVarDecl : mkContVarDecl : mkContLVarDecl : mkMagicVarDecl : tvar : (wires ++ gvars ++ fvars ++ cvars ++ tvars ++ ivars ++ fpvars ++ pvars), 
          tenum)
    where
    -- tag: one enumerator per controllable task
    (tvar, tenum) = mkTagVarDecl

    -- global variables
    gvars = let ?scope = ScopeTemplate tmMain 
                in map (\v -> mkVarDecl (varMem $ gvarVar v) (NSID Nothing Nothing) (gvarVar v)) $ tmVar tmMain

    -- wires
    wires = let ?scope = ScopeTemplate tmMain 
                in map (mkVarDecl False (NSID Nothing Nothing)) $ tmWire tmMain

    -- local variables and input arguments of functions and procedures
    fvars = concatMap (\m -> (let ?scope = ScopeMethod tmMain m 
                                  in map (\v -> mkVarDecl (varMem v) (NSID Nothing (Just m)) v) (methVar m)) 
                              ++
                             (let ?scope = ScopeTemplate tmMain 
                                  in map (mkVarDecl False (NSID Nothing (Just m))) 
                                         (filter ((==ArgIn) . argDir) (methArg m))))
                      $ filter ((flip elem) [Function, Procedure] . methCat) 
                      $ tmMethod tmMain

    -- For each controllable task:
    -- * local variables, input arguments, output arguments, retval
    cvars = concatMap (taskVars Nothing True)
                      $ filter ((== Task Controllable) . methCat)
                      $ tmMethod tmMain

    -- For each task in the process tree:
    -- * local variables, input arguments, output arguments, retval
    -- * enabling variable
    tvars = concatMap (concat . mapPTreeTask (\pid m -> (mkEnVarDecl pid (Just m)) : (taskVars (Just pid) True m)))
                      $ tmProcess tmMain

    -- For each inlined task: 
    -- * local variables, input arguments, output arguments
    ivars = concatMap (concat . mapPTreeInlinedTask (\pid m -> taskVars (Just pid) False m))
                      $ tmProcess tmMain

    -- For each root process:
    -- * local variables
    pvars = concatMap (\p -> map (\v -> let ?scope = ScopeProcess tmMain p 
                                        in mkVarDecl (varMem v) (NSID (Just $ PrID (sname p) []) Nothing) v) (procVar p)) 
                      $ tmProcess tmMain

    -- For each forked process:
    -- * enabling variable
    fpvars = concatMap (mapPTreeFProc (\pid _ -> mkEnVarDecl pid Nothing))
                       $ tmProcess tmMain

    taskVars :: Maybe PrID -> Bool -> Method -> [I.Var]
    taskVars mpid ret m = 
        (let ?scope = ScopeMethod tmMain m in map (\v -> mkVarDecl (varMem v) (NSID mpid (Just m)) v) (methVar m)) ++ 
        (let ?scope = ScopeMethod tmMain m in map (mkVarDecl False (NSID mpid (Just m))) (methArg m)) ++
        (if ret then maybeToList (mkRetVarDecl mpid m) else [])

----------------------------------------------------------------------
-- CFA transformation
----------------------------------------------------------------------

-- Convert normal or forked process to CFA
procToCFA :: (?spec::Spec, ?procs::[I.Process], ?solver::SMTSolver) => PrID -> NameMap -> Scope -> Statement -> (I.CFA, [I.Var])
procToCFA pid@(PrID _ ps) lmap parscope stat = I.cfaTraceFile (ctxCFA ctx') (show pid) $ (ctxCFA ctx', ctxVar ctx')
    where -- top-level processes are not guarded
          guarded = not $ null ps
          guard = if guarded 
                     then mkEnVar pid Nothing I.=== I.true
                     else I.true
          -- Add process-local variables to nmap
          ctx = CFACtx { ctxCID     = Just $ UCID pid Nothing 
                       , ctxStack   = [(parscope, error "return from a process", Nothing, lmap)]
                       , ctxCFA     = I.newCFA parscope stat guard
                       , ctxBrkLocs = error "break outside a loop"
                       , ctxGNMap   = globalNMap
                       , ctxLastVar = 0
                       , ctxVar     = []}
          ctx' = execState (do aftguard <- if guarded
                                              then ctxInsTrans' I.cfaInitLoc $ I.TranStat $ I.SAssume guard
                                              else return I.cfaInitLoc
                               aft <- procStatToCFA stat aftguard
                               _   <- ctxFinal aft
                               ctxPruneUnreachable) ctx

-- Convert controllable or uncontrollable task to CFA.
taskToCFA :: (?spec::Spec, ?procs::[I.Process], ?solver::SMTSolver) => Maybe PrID -> Method -> (I.CFA, [I.Var])
taskToCFA mpid meth = I.cfaTraceFile (ctxCFA ctx') (maybe "" show mpid ++ "_" ++ sname meth) $ (ctxCFA ctx', ctxVar ctx')
    where guard = maybe (mkTagVar I.=== tagMethod meth) (\pid -> mkEnVar pid (Just meth) I.=== I.true) mpid
          reset = maybe (mkTagVar I.=: tagIdle)         (\pid -> mkEnVar pid (Just meth) I.=: I.false) mpid
          sc    = ScopeMethod tmMain meth
          stat = fromRight $ methBody meth
          ctx = CFACtx { ctxCID     = maybe (Just $ CTCID meth) (\pid -> Just $ UCID pid (Just meth)) mpid
                       , ctxStack   = []
                       , ctxCFA     = I.newCFA sc stat guard
                       , ctxBrkLocs = error "break outside a loop"
                       , ctxGNMap   = globalNMap
                       , ctxLastVar = 0
                       , ctxVar     = []}
          ctx' = execState (do aftguard <- ctxInsTrans' I.cfaInitLoc $ I.TranStat $ I.SAssume guard
                               aftcall  <- ctxInsTrans' aftguard $ I.TranCall meth Nothing
                               retloc   <- ctxInsLoc
                               aftreset <- ctxInsTrans' retloc (I.TranStat reset)
                               aftsuf   <- ctxInsLoc
                               ctxPushScope sc retloc (mkRetVar mpid meth) (methodLMap mpid meth)
                               ctxSuffix aftreset aftsuf I.cfaInitLoc                               
                               ctxInsTrans aftsuf I.cfaInitLoc I.TranReturn
                               aftbody  <- procStatToCFA stat aftcall
                               ctxInsTrans aftbody retloc I.TranNop
                               ctxPruneUnreachable) ctx

-- Recursively construct CFA's for the process and its children
procToCProc :: (?spec::Spec, ?solver::SMTSolver) => Process -> (I.Process, [I.Var])
procToCProc p = fprocToCProc Nothing ((ScopeProcess tmMain p), (sname p, (procStatement p)))

fprocToCProc :: (?spec::Spec, ?solver::SMTSolver) => Maybe PrID -> (Scope, (String, Statement)) -> (I.Process, [I.Var])
fprocToCProc mparpid (sc, (n,stat)) = (I.Process{..}, pvs ++ concat tvs ++ concat cvs)
    where lmap                = scopeLMap mparpid sc 
          pid                 = maybe (PrID n []) (\parpid -> childPID parpid n) mparpid
          procName            = n
          (procChildren, cvs) = unzip $ map (fprocToCProc $ Just pid) $ forkedProcsRec sc stat
          (procCFA,pvs)       = let ?procs = procChildren in procToCFA pid lmap sc stat
          (procTask,tvs)      = unzip
                                $ map (let ?procs = procChildren in taskToCTask pid)
                                $ filter (((flip elem) [Task Controllable, Task Uncontrollable]) . methCat)
                                $ procCallees sc stat

taskToCTask :: (?spec::Spec, ?procs::[I.Process], ?solver::SMTSolver) => PrID -> Method -> (I.Task, [I.Var])
taskToCTask pid meth = (I.Task{..}, vs)
    where taskMethod    = meth
          (taskCFA, vs) = taskToCFA (Just pid) meth

-- Map a function over all inlined tasks called by the process
mapPTreeInlinedTask :: (?spec::Spec) => (PrID -> Method -> a) -> Process -> [a]
mapPTreeInlinedTask f p = mapPTreeInlinedTask' f (PrID (sname p) []) (ScopeProcess tmMain p) (procStatement p)

mapPTreeInlinedTask' :: (?spec::Spec) => (PrID -> Method -> a) -> PrID -> Scope -> Statement -> [a]
mapPTreeInlinedTask' f pid s stat = 
    (concatMap (\m -> (f pid m) : (mapPTreeInlinedTask' f pid (ScopeMethod tmMain m) (fromRight $ methBody m)))
               $ filter ((==Task Invisible) . methCat)
               $ procCallees s stat)
    ++
    (concatMap (\(n,st) -> mapPTreeInlinedTask' f (childPID pid n) s st) $ forkedProcs stat)


-- Map a function over all tasks called by the process
mapPTreeTask :: (?spec::Spec) => (PrID -> Method -> a) -> Process -> [a]
mapPTreeTask f p = mapPTreeTask' f (PrID (sname p) []) (ScopeProcess tmMain p) (procStatement p)

mapPTreeTask' :: (?spec::Spec) => (PrID -> Method -> a) -> PrID -> Scope -> Statement -> [a]
mapPTreeTask' f pid s stat = 
    (concatMap (\m -> (f pid m) : (mapPTreeTask' f pid (ScopeMethod tmMain m) (fromRight $ methBody m)))
               $ filter (((flip elem) [Task Controllable, Task Uncontrollable]) . methCat)
               $ procCallees s stat)
    ++
    (concatMap (\(n,st) -> mapPTreeTask' f (childPID pid n) s st) $ forkedProcs stat)

-- Map a function over forked processes
mapPTreeFProc :: (?spec::Spec) => (PrID -> Statement -> a) -> Process -> [a]
mapPTreeFProc f p = mapPTreeFProc' f (PrID (sname p) []) (ScopeProcess tmMain p) (procStatement p)

mapPTreeFProc' :: (?spec::Spec) => (PrID -> Statement -> a) -> PrID -> Scope -> Statement -> [a]
mapPTreeFProc' f pid s stat = 
    case pid of 
         PrID _ [] -> []
         _         -> [f pid stat]
    ++
    (concatMap (\(s',(n,st)) -> mapPTreeFProc' f (childPID pid n) s' st) $ forkedProcsRec s stat)


-- Find all methods invoked by the statement in the context of the current process,
-- i.e., not inside fork blocks
procCallees :: (?spec::Spec) => Scope -> Statement -> [Method]
procCallees s stat = 
   map (\n -> snd $ getMethod s (MethodRef nopos [n]))
       $ S.toList $ S.fromList $ map (name . snd . getMethod s) $ procCalleesRec s stat

procCallees' :: (?spec::Spec) => Scope -> Statement -> [MethodRef]
procCallees' s (SSeq     _ ss)                  = concatMap (procCallees' s) ss
procCallees' s (SForever _ b)                   = procCallees' s b
procCallees' s (SDo      _ b _)                 = procCallees' s b
procCallees' s (SWhile   _ _ b)                 = procCallees' s b
procCallees' s (SFor     _ (i,_,u) b)           = (fromMaybe [] $ fmap (procCallees' s) i) ++ procCallees' s u ++ procCallees' s b
procCallees' s (SChoice  _ ss)                  = concatMap (procCallees' s) ss
procCallees' _ (SInvoke  _ mref _)              = [mref]
procCallees' _ (SAssign  _ _ (EApply _ mref _)) = [mref]
procCallees' s (SITE     _ _ t me)              = procCallees' s t ++ (fromMaybe [] $ fmap (procCallees' s) me)
procCallees' s (SCase    _ _ cs md)             = concatMap (\(_,st) -> procCallees' s st) cs ++
                                                  (fromMaybe [] $ fmap (procCallees' s) md)
procCallees' _ _                                = []

procCalleesRec :: (?spec::Spec) => Scope -> Statement -> [MethodRef]
procCalleesRec s stat = ms1 ++ ms2
    where ms1 = procCallees' s stat
          ms2 = concatMap (procCalleesRec s . fromRight . methBody . snd . getMethod s) ms1

-- Find processes forked by the statement
forkedProcs :: (?spec::Spec) => Statement -> [(String, Statement)]
forkedProcs (SSeq _ ss)              = concatMap forkedProcs ss
forkedProcs (SPar _ ps)              = map (mapFst sname) ps
forkedProcs (SForever _ b)           = forkedProcs b
forkedProcs (SDo _ b _)              = forkedProcs b
forkedProcs (SWhile _ _ b)           = forkedProcs b
forkedProcs (SFor _ (minit, _, i) b) = fromMaybe [] (fmap forkedProcs minit) ++ forkedProcs i ++ forkedProcs b
forkedProcs (SChoice _ ss)           = concatMap forkedProcs ss
forkedProcs (SITE _ _ t me)          = forkedProcs t ++ fromMaybe [] (fmap forkedProcs me)
forkedProcs (SCase _ _ cs mdef)      = concatMap (forkedProcs . snd) cs ++
                                       fromMaybe [] (fmap forkedProcs mdef)
forkedProcs _                        = []

-- Recurse over task invocations
forkedProcsRec :: (?spec::Spec) => Scope -> Statement -> [(Scope, (String, Statement))]
forkedProcsRec s stat = 
    (map (s,) $ forkedProcs stat) ++
    (concatMap (\m -> map (ScopeMethod tmMain m,) $ forkedProcs $ fromRight $ methBody m) (procCallees s stat))

---------------------------------------------------------------
-- CFA to LTS transformation
---------------------------------------------------------------

cfaToITransition :: I.CFA -> String -> I.Transition
cfaToITransition cfa fname = case trans of
                                  [t] -> I.cfaTraceFile (I.tranCFA t) fname $ t
                                  _   -> error $ "cfaToITransition: Invalid CFA:\n" ++ (intercalate "\n\n"  $ map show trans)
      where trans = locTrans cfa I.cfaInitLoc

-- Convert CFA to a list of transitions.
-- Assume that unreachable states have already been pruned.
cfaToITransitions :: CID -> I.CFA -> [I.Transition]
cfaToITransitions cid cfa = I.cfaTraceFileMany (map I.tranCFA trans') ("tran_" ++ show cid) trans'
    where
    -- compute a set of transitions for each location labelled with pause or final
    states = I.cfaDelayLocs cfa
    trans = concatMap (locTrans cfa) states
    trans' = map (extractTransition cid) trans


locTrans :: I.CFA -> I.Loc -> [I.Transition]
locTrans cfa loc =
    let -- compute all reachable locations before pause
        r = I.cfaReachInst cfa loc
        -- construct subgraph with only these nodes
        cfa' = I.cfaPrune cfa (S.insert loc r)
        -- (This is a good place to check for loop freedom.)
        -- for each final location, compute a subgraph that connects the two
        dsts = filter (I.isDelayLabel . fromJust . G.lab cfa) $ S.toList r 
    in map (\dst -> I.Transition loc dst $ pruneTrans cfa' loc dst) dsts

-- iteratively prune dead-end locations until only transitions connecting from and to remain
pruneTrans :: I.CFA -> I.Loc -> I.Loc -> I.CFA
pruneTrans cfa from to = if G.noNodes cfa'' == G.noNodes cfa then cfa'' else pruneTrans cfa'' from to
    where -- eliminate from-->from loops and to-->... transitions, unless we are generating a loop transition
          cfa' = if from /= to
                    then foldl' (\cfa0 (f,t,_) -> G.delEdge (f,t) cfa0) cfa $ G.inn cfa from ++ G.out cfa to
                    else cfa
          cfa'' = foldl' (\g loc -> if loc /= to && null (G.suc g loc) then G.delNode loc g else g) cfa' (G.nodes cfa') 

-- Extract transition into a separate CFA
extractTransition :: CID -> I.Transition -> I.Transition
extractTransition cid (I.Transition from to cfa) = 
    let -- If this is a loop transition, split the initial node
        (linit, lfinal, cfa1) = if from == to
                                   then splitLoc from cfa
                                   else (from, to, cfa)
        (cfa2, befpc) = I.cfaInsLoc (I.LInst I.ActNone) cfa1
        -- check PC value before the transition
        cfa3 = I.cfaInsTrans befpc linit (I.TranStat $ I.SAssume $ mkPCVar cid I.=== mkPC cid from) cfa2
    in I.Transition befpc lfinal cfa3

tranAppend :: I.Transition -> I.Statement -> I.Transition
tranAppend (I.Transition from to cfa) s = I.Transition from to' cfa'
    where (cfa', to') = I.cfaInsTrans' to (I.TranStat s) cfa

-- Split location into 2, one containing all outgoing edges and one containing
-- all incoming edges of the original location
splitLoc :: I.Loc -> I.CFA -> (I.Loc, I.Loc, I.CFA)
splitLoc loc cfa = (loc, loc', cfa3)
    where i            = G.inn cfa loc
          cfa1         = foldl' (\cfa0 (f,t,_) -> G.delEdge (f,t) cfa0) cfa i 
          (cfa2, loc') = I.cfaInsLoc (I.LInst I.ActNone) cfa1
          cfa3         = foldl' (\cfa0 (f,_,l) -> G.insEdge (f,loc',l) cfa0) cfa2 i
