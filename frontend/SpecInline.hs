{-# LANGUAGE ImplicitParams, TupleSections #-}

-- Convert flattened spec to internal representation
module SpecInline (spec2Internal) where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import qualified Data.Graph.Inductive.Graph as G
import Debug.Trace

import Util hiding (name,trace)
import TSLUtil
import Spec
import qualified ISpec as I
import qualified IExpr as I
import qualified CFA   as I
import qualified IType as I
import qualified IVar  as I
import Pos
import Name
import NS
import Statement
import StatementOps
import StatementInline
import Expr
import ExprOps
import ExprInline
import Template
import TemplateFlatten
import TVar
import Method
import Process
import Type
import TypeOps
import Inline

-- Main function
spec2Internal :: Spec -> I.Spec
spec2Internal s = 
    let ?spec = specSimplify s -- preprocessing
    in let senum = mapMaybe (\d -> case tspec d of
                                        EnumSpec _ es -> Just $ I.Enumeration (sname d) (map sname es)
                                        _             -> Nothing) (specType ?spec)
           (vars, tagenum, auxinit) = mkVars
           -- Controllable transitions
           (ctran, cvars) = unzip $ map mkCTran $ filter ((== Task Controllable) . methCat) $ tmMethod tmMain
           -- Uncontrollable processes
           uproc = concatMap procTree $ tmProcess tmMain
           cproc = map (\m -> let ?procs = [] in cfaToIProcess [sname m] $ taskToCFA [] m True) 
                       $ filter ((== Task Controllable) . methCat)
                       $ tmMethod tmMain
           -- PC variables, associated enums and initial assignments.
           -- Only create PC variables for processes with >1 states.
           (pcvars, pcenums, pcinit) = unzip3 
                                       $ mapMaybe (\p -> let pid = pPID p
                                                             enum = pPCEnum p
                                                             var  = I.Var False I.VarState (mkPCVarName pid) (I.Enum $ I.enumName enum)
                                                             init = mkPCVar pid I.=== mkPC pid I.cfaInitLoc
                                                         in if null $ I.enumEnums enum then Nothing else Just (var, enum, init))
                                                  $ uproc ++ cproc
           (pidvar, pidenum) = mkPIDVarDecl $ map pPID $ cproc ++ uproc
           -- Uncontrollable transitions
           utran = concatMap pBody uproc
       in I.Spec { I.specEnum   = pidenum : tagenum : (senum ++ pcenums)
                 , I.specVar    = pidvar : (pcvars ++ vars) ++ 
                                  concat cvars ++ 
                                  concatMap pVar cproc ++ 
                                  concatMap pVar uproc
                 , I.specCTran  = mkMagicReturn : ctran
                 , I.specUTran  = mkIdleTran : utran
                 , I.specWire   = mkWires
                 , I.specInit   = (mkInit, I.conj $ (auxinit : pcinit))
                 , I.specGoal   = mkMagicGoal : (map mkGoal $ tmGoal tmMain)
                 , I.specFair   = mkFair $ cproc ++ uproc
                 }


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
                        ?uniq = newUniq
                    in p { procStatement = statSimplify $ procStatement p}

methSimplify :: (?spec::Spec) => Template -> Method -> Method
methSimplify tm m = let ?scope = ScopeMethod tm m
                        ?uniq = newUniq
                    in m { methBody = Right $ statSimplify $ fromRight $ methBody m}

----------------------------------------------------------------------
-- Wires
----------------------------------------------------------------------

-- Generate transition that assigns all wire variables.  It will be
-- implicitly prepended to all "regular" transitions.
mkWires :: (?spec::Spec) => I.Transition
mkWires = 
    let wires = orderWires
        -- Generate assignment statement for each wire
        stat = let ?scope = ScopeTemplate tmMain
                   ?uniq  = newUniq
               in statSimplify $ SSeq nopos $ map (\w -> SAssign nopos (ETerm nopos [name w]) (fromJust $ wireRHS w)) wires
        ctx = CFACtx { ctxPID     = []
                     , ctxScope   = ScopeTemplate tmMain
                     , ctxCFA     = I.newCFA I.true
                     , ctxRetLoc  = error "return from a wire assignment"
                     , ctxBrkLoc  = error "break outside a loop"
                     , ctxLHS     = Nothing
                     , ctxGNMap   = globalNMap
                     , ctxLNMap   = M.empty
                     , ctxLastVar = 0
                     , ctxVar     = []}
        ctx' = let ?procs =[] in execState (do aft <- procStatToCFA stat I.cfaInitLoc
                                               ctxPause aft I.true) ctx
        trans = I.cfaTraceFile (ctxCFA ctx') "wires_cfa" $ locTrans (ctxCFA ctx') I.cfaInitLoc
    in case trans of
            [t] -> I.cfaTraceFile (I.tranCFA t) "wires" $ t
            _   -> error $ "mkWires: Invalid wire expression.\nstat:" ++ show stat ++ "\ntrans:\n" ++ (intercalate "\n\n"  $ map show trans)


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
    where (g',ord) = foldl' (\(g,ord) n -> if null $ G.suc g n then (G.delNode n g, ord++[n]) else (g,ord))
                            (g,[]) (G.nodes g)


----------------------------------------------------------------------
-- Fair sets
----------------------------------------------------------------------

mkFair :: (?spec::Spec) => [ProcTrans] -> [I.Expr]
mkFair procs = fsched : fproc
    where -- Fair scheduling:  GF (not ($magic==true && $cont == false))
          fsched = I.conj [mkMagicVar I.=== I.true, mkContVar I.=== I.false]

          -- For each state s of uncontrollable process pid with wait condition cond:
          -- GF (not (pc=s && cond && lastpid == pid)) 
          fproc = concatMap (\p -> let pid = pPID p
                                   in map (\(loc,cond) -> I.conj [mkPCVar pid I.=== mkPC pid loc, cond, mkPIDVar I.=== mkPIDEnum pid]) 
                                          $ pPauses p) 
                            procs 

----------------------------------------------------------------------
-- Init and goal conditions
----------------------------------------------------------------------

mkInit :: (?spec::Spec) => I.Transition
mkInit = mkCond "$init" cond []
    where -- conjunction of initial variable assignments
          ass = mapMaybe (\v -> case varInit $ gvarVar v of
                                     Nothing -> Nothing
                                     Just e  -> Just (EBinOp (pos v) Eq (ETerm nopos $ [name v]) e)) (tmVar tmMain)
          -- add init blocks
          cond = eAnd nopos (ass ++ map initBody (tmInit tmMain))

-- $err == false
noerror :: I.Expr
noerror = I.EUnOp Not mkErrVar

mkGoal :: (?spec::Spec) => Goal -> I.Goal
mkGoal g = -- Add $err==false to the goal condition
           I.Goal (sname g) (mkCond (sname g) (goalCond g) [noerror])

-- In addition to regular goals, we are required to be outside a magic block
-- infinitely often
mkMagicGoal :: (?spec::Spec) => I.Goal
mkMagicGoal = I.Goal "$magic_goal" $ mkCond "$magic_goal" (EBool nopos True) [I.EUnOp Not mkMagicVar, noerror]

mkCond :: (?spec::Spec) => String -> Expr -> [I.Expr] -> I.Transition
mkCond descr e extra = 
    let -- simplify and convert into a statement
        (ss, cond') = let ?scope = ScopeTemplate tmMain 
                          ?uniq = newUniq
                      in exprSimplify e
        stat = SSeq nopos (ss ++ [SAssume nopos cond'])

        ctx = CFACtx { ctxPID     = []
                     , ctxScope   = ScopeTemplate tmMain
                     , ctxCFA     = I.newCFA I.true
                     , ctxRetLoc  = error $ "return from " ++ descr
                     , ctxBrkLoc  = error "break outside a loop"
                     , ctxLHS     = Nothing
                     , ctxGNMap   = globalNMap
                     , ctxLNMap   = M.empty
                     , ctxLastVar = 0
                     , ctxVar     = []}
        ctx' = let ?procs =[] in execState (do aft <- procStatToCFA stat I.cfaInitLoc
                                               ctxPause aft I.true) ctx

        trans = locTrans (ctxCFA ctx') I.cfaInitLoc
        -- precondition
    in case trans of
            [t] -> let res = foldl' tranAppend t (map I.SAssume extra)
                   in I.cfaTraceFile (I.tranCFA t) descr $ res
            _   -> error $ "mkCond " ++ show e ++ ": Invalid condition"

----------------------------------------------------------------------
-- Idle transition
----------------------------------------------------------------------

mkIdleTran :: (?spec::Spec) => I.Transition
mkIdleTran =
    let (cfa0, aftguard) = I.cfaInsTrans' I.cfaInitLoc (I.SAssume $ mkContVar I.=== I.false) (I.newCFA I.true)
    in utranSuffix pidIdle False True (I.Transition I.cfaInitLoc aftguard cfa0)

----------------------------------------------------------------------
-- Controllable transitions
----------------------------------------------------------------------

-- only allow controllable transitions when inside a magic block and in
-- a controllable state
contGuard = I.SAssume $ I.conj $ [mkMagicVar I.=== I.true, mkContVar I.=== I.true]

mkCTran :: (?spec::Spec) => Method -> (I.Transition, [I.Var])
mkCTran m = (I.Transition I.cfaInitLoc after cfa4, vs)
    where (cfa0, aftguard) = I.cfaInsTrans' I.cfaInitLoc contGuard (I.newCFA I.true)
          -- tag
          (cfa1, afttag)   = I.cfaInsTrans' aftguard (mkTagVar I.=: tagMethod m) cfa0
          -- arguments
          ((cfa2, aftargs), _, vs)  = let ?scope = ScopeMethod tmMain m
                                      in foldl' (\((cfa,loc),last,vs) arg -> 
                                                  let n    = mkVarNameS Nothing (Just m) ("$tmp" ++ show (last+1))
                                                      t    = mkType $ typ arg
                                                      v    = I.Var False I.VarTmp n t
                                                      asns = zipWith I.SAssign (I.exprScalars (mkVar Nothing (Just m) arg) t)
                                                                               (I.exprScalars (I.EVar n) t)
                                                      cfa' = I.cfaInsTransMany' loc asns cfa
                                                  in (cfa', last+1, v:vs))
                                                ((cfa1, afttag), 0, []) $ filter ((==ArgIn) . argDir) (methArg m)
          -- switch to uncontrollable state
          (cfa3, aftcont)  = I.cfaInsTrans' aftargs (mkContVar I.=: I.false)           cfa2
          -- $pid = $pidcont
          (cfa4, after)    = I.cfaInsTrans' aftcont (mkPIDVar  I.=: mkPIDEnum pidCont) cfa3

mkMagicReturn :: (?spec::Spec) => I.Transition
mkMagicReturn = I.Transition I.cfaInitLoc after cfa2
    where (cfa0, aftguard) = I.cfaInsTrans' I.cfaInitLoc contGuard               (I.newCFA I.true)
          (cfa1, aftmagic) = I.cfaInsTrans' aftguard   (mkMagicVar I.=: I.false) cfa0
          (cfa2, after)    = I.cfaInsTrans' aftmagic   (mkContVar I.=: I.false)  cfa1

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------

mkVars :: (?spec::Spec) => ([I.Var], I.Enumeration, I.Expr)
mkVars = (mkErrVarDecl : mkNullVarDecl : mkContVarDecl : mkMagicVarDecl : tvar : (wires ++ gvars ++ fvars ++ cvars ++ tvars ++ pvars), 
          tenum, 
          I.conj $ teninit ++ peninit ++ [errinit, taginit, maginit, continit, pidinit])
    where
    -- tag: one enumerator per controllable task
    (tvar, tenum) = mkTagVarDecl

    -- global variables
    gvars = let ?scope = ScopeTemplate tmMain 
                in map (\v -> mkVarDecl (varMem $ gvarVar v)Nothing Nothing (gvarVar v)) $ tmVar tmMain

    -- wires
    wires = let ?scope = ScopeTemplate tmMain 
                in map (mkVarDecl False Nothing Nothing) $ tmWire tmMain

    -- local variables and input arguments of functions and procedures
    fvars = concatMap (\m -> (let ?scope = ScopeMethod tmMain m 
                                  in map (\v -> mkVarDecl (varMem v) Nothing (Just m) v) (methVar m)) 
                              ++
                             (let ?scope = ScopeTemplate tmMain 
                                  in map (mkVarDecl False Nothing (Just m)) 
                                         (filter ((==ArgIn) . argDir) (methArg m))))
                      $ filter ((flip elem) [Function, Procedure] . methCat) 
                      $ tmMethod tmMain

    -- For each controllable task:
    -- * local variables, input arguments, output arguments, retval
    cvars = concatMap (taskVars Nothing)
                      $ filter ((== Task Controllable) . methCat)
                      $ tmMethod tmMain

    -- For each task in the process tree:
    -- * local variables, input arguments, output arguments, retval
    -- * enabling variable
    tvars = concatMap (concat . mapPTreeTask (\pid m -> (mkEnVarDecl pid (Just m)) : (taskVars (Just pid) m)))
                      $ tmProcess tmMain

    -- For each forked process:
    -- * enabling variable
    pvars = concatMap (mapPTreeFProc (\pid _ -> mkEnVarDecl pid Nothing))
                      $ tmProcess tmMain

    -- Initialise $en vars to false
    teninit = concatMap (mapPTreeTask (\pid m -> mkEnVar pid (Just m) I.=== I.false)) $ tmProcess tmMain
    peninit = concatMap (mapPTreeFProc (\pid _ -> mkEnVar pid Nothing  I.=== I.false)) $ tmProcess tmMain

    -- Initialise $tag, $magic, $cont
    taginit  = mkTagVar   I.=== tagIdle
    maginit  = mkMagicVar I.=== I.false
    continit = mkContVar  I.=== I.false
    pidinit  = mkPIDVar   I.=== mkPIDEnum pidIdle
    errinit  = mkErrVar   I.=== I.false

    taskVars :: Maybe PID -> Method -> [I.Var]
    taskVars mpid m = 
        (let ?scope = ScopeTemplate tmMain in map (\v -> mkVarDecl (varMem v) mpid (Just m) v) (methVar m)) ++ 
        (let ?scope = ScopeMethod tmMain m in map (mkVarDecl False mpid (Just m)) (methArg m)) ++
        maybeToList (mkRetVarDecl mpid m)

----------------------------------------------------------------------
-- CFA transformation
----------------------------------------------------------------------

-- Convert process to CFA
-- For a forked process the mparpid argument is the PID of the process in 
-- whose syntactic scope the present process is located.
procToCFA :: (?spec::Spec, ?procs::[ProcTrans]) => PID -> Process -> (I.CFA, [I.Var])
procToCFA pid proc = I.cfaTraceFile (ctxCFA ctx') (pidToName pid) $ (ctxCFA ctx', ctxVar ctx')
    where ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = ScopeProcess tmMain proc
                       , ctxCFA    = I.newCFA I.true
                       , ctxRetLoc = error "return from a process"
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = Nothing
                       , ctxGNMap  = globalNMap
                       , ctxLNMap  = procLMap pid proc
                       , ctxLastVar = 0
                       , ctxVar     = []}
          ctx' = execState (do aft <- procStatToCFA (procStatement proc) I.cfaInitLoc
                               ctxFinal aft) ctx

-- Convert forked process to CFA
fprocToCFA :: (?spec::Spec, ?procs::[ProcTrans]) => PID -> NameMap -> Scope -> Statement -> (I.CFA, [I.Var])
fprocToCFA pid lmap parscope stat = I.cfaTraceFile (ctxCFA ctx') (pidToName pid) $ (ctxCFA ctx', ctxVar ctx')
    where guard = mkEnVar pid Nothing I.=== I.true
          -- Add process-local variables to nmap
          ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = parscope
                       , ctxCFA    = I.newCFA guard
                       , ctxRetLoc = error "return from a forked process"
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = Nothing
                       , ctxGNMap  = globalNMap
                       , ctxLNMap  = lmap
                       , ctxLastVar = 0
                       , ctxVar     = []}
          ctx' = execState (do aftguard <- ctxInsTrans' I.cfaInitLoc $ I.SAssume guard
                               final <- procStatToCFA stat aftguard
                               ctxFinal final) ctx

-- Convert controllable or uncontrollable task to CFA.
-- The ctl argument indicates that a controllable transition is to be
-- generated (using tag instead of enabling variable)
taskToCFA :: (?spec::Spec, ?procs::[ProcTrans]) => PID -> Method -> Bool -> (I.CFA, [I.Var])
taskToCFA pid meth ctl = I.cfaTraceFile (ctxCFA ctx') (pidToName pid ++ "_" ++ sname meth) $ (ctxCFA ctx', ctxVar ctx')
    where guard = if ctl
                     then mkTagVar I.=== tagMethod meth
                     else mkEnVar pid (Just meth) I.=== I.true
          stat = fromRight $ methBody meth
          ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = ScopeMethod tmMain meth
                       , ctxCFA    = I.newCFA guard
                       , ctxRetLoc = I.cfaInitLoc
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = mkRetVar (Just pid) meth
                       , ctxGNMap  = globalNMap
                       , ctxLNMap  = methodLMap pid meth
                       , ctxLastVar = 0
                       , ctxVar     = []}
          ctx' = if ctl
                    then execState (do aftguard <- ctxInsTrans' I.cfaInitLoc $ I.SAssume guard
                                       -- reset tag to idle on return
                                       retloc  <- ctxInsLoc
                                       ctxInsTrans retloc I.cfaInitLoc $ mkTagVar I.=: tagIdle
                                       ctxPutRetLoc retloc
                                       aftbody <- procStatToCFA stat aftguard
                                       ctxInsTrans aftbody retloc I.nop) 
                                   ctx
                    else execState (do aftguard <- ctxInsTrans' I.cfaInitLoc $ I.SAssume guard
                                       -- reset $en to false on return
                                       retloc  <- ctxInsLoc
                                       ctxInsTrans retloc I.cfaInitLoc $ (mkEnVar pid (Just meth)) I.=: I.false
                                       ctxPutRetLoc retloc
                                       aftbody <- procStatToCFA stat aftguard
                                       ctxInsTrans aftbody retloc I.nop) 
                                   ctx


-- Recursively construct LTS for the process and its children
procTree :: (?spec::Spec) => Process -> [ProcTrans]
procTree p = 
    let pid      = [sname p]
        scope    = ScopeProcess tmMain p
        children = procTreeRec pid scope (procStatement p) (procLMap pid p)
        iproc    = let ?procs = children in cfaToIProcess pid $ procToCFA pid p
    in iproc : children

fprocTree :: (?spec::Spec) => PID -> Scope -> NameMap -> (Ident, Statement) -> [ProcTrans]
fprocTree parpid parscope lmap (n,stat) = 
    let pid      = parpid ++ [sname n]
        children = procTreeRec pid parscope stat lmap
        iproc    = let ?procs = children in cfaToIProcess pid $ fprocToCFA pid lmap parscope stat
    in iproc : children

taskProcTree :: (?spec::Spec) => PID -> Method -> [ProcTrans]
taskProcTree parpid meth = 
    let pid      = parpid ++ [sname meth]
        children = procTreeRec parpid (ScopeMethod tmMain meth) (fromRight $ methBody meth) (methodLMap parpid meth)
        iproc    = let ?procs = children in cfaToIProcess pid $ taskToCFA parpid meth False
    in iproc : children

-- Recursive step of the algorithm: find all child subprocesses of a statement
procTreeRec :: (?spec::Spec) => PID -> Scope -> Statement -> NameMap -> [ProcTrans]
procTreeRec pid scope stat lmap = tasks ++ forked
    where
    -- controllable/uncontrollable tasks invoked by the process
    tasks  = concatMap (taskProcTree pid)
             $ filter (((flip elem) [Task Controllable, Task Uncontrollable]) . methCat)
             $ procCallees scope stat
    -- spawned processes
    forked = concatMap (fprocTree pid scope lmap) $ forkedProcs stat
    
-- Map a function over all tasks called by the process
mapPTreeTask :: (?spec::Spec) => (PID -> Method -> a) -> Process -> [a]
mapPTreeTask f p = mapPTreeTask' f [sname p] (ScopeProcess tmMain p) (procStatement p)

mapPTreeTask' :: (?spec::Spec) => (PID -> Method -> a) -> PID -> Scope -> Statement -> [a]
mapPTreeTask' f pid s stat = 
    (concatMap (\m -> (f pid m) : (mapPTreeTask' f pid (ScopeMethod tmMain m) (fromRight $ methBody m)))
               $ filter (((flip elem) [Task Controllable, Task Uncontrollable]) . methCat)
               $ procCallees s stat)
    ++
    (concatMap (\(n,st) -> mapPTreeTask' f (pid++[sname n]) s st) $ forkedProcs stat)

-- Map a function over forked processes
mapPTreeFProc :: (?spec::Spec) => (PID -> Statement -> a) -> Process -> [a]
mapPTreeFProc f p = mapPTreeFProc' f [sname p] (ScopeProcess tmMain p) (procStatement p)

mapPTreeFProc' :: (?spec::Spec) => (PID -> Statement -> a) -> PID -> Scope -> Statement -> [a]
mapPTreeFProc' f pid s stat = 
    case pid of 
         [n] -> [f pid stat]
         _   -> []
    ++
    (concatMap (\(s',(n,st)) -> mapPTreeFProc' f (pid++[sname n]) s' st) $ forkedProcsRec s stat)


-- Find all methods invoked by the statement in the context of the current process,
-- i.e., not inside fork blocks
procCallees :: (?spec::Spec) => Scope -> Statement -> [Method]
procCallees s stat = 
   map (\n -> snd $ getMethod s (MethodRef nopos [n]))
       $ S.toList $ S.fromList $ map (name . snd . getMethod s) $ procCalleesRec s stat

procCallees' :: (?spec::Spec) => Scope -> Statement -> [MethodRef]
procCallees' s (SSeq     _ ss)                   = concatMap (procCallees' s) ss
procCallees' s (SForever _ b)                    = procCallees' s b
procCallees' s (SDo      _ b c)                  = procCallees' s b
procCallees' s (SWhile   _ c b)                  = procCallees' s b
procCallees' s (SFor     _ (i,c,u) b)            = (fromMaybe [] $ fmap (procCallees' s) i) ++ procCallees' s u ++ procCallees' s b
procCallees' s (SChoice  _ ss)                   = concatMap (procCallees' s) ss
procCallees' s (SInvoke  _ mref as)              = [mref]
procCallees' s (SAssign  _ l (EApply _ mref as)) = [mref]
procCallees' s (SITE     _ c t me)               = procCallees' s t ++ (fromMaybe [] $ fmap (procCallees' s) me)
procCallees' s (SCase    _ c cs md)              = concatMap (\(_,st) -> procCallees' s st) cs ++
                                                   (fromMaybe [] $ fmap (procCallees' s) md)
procCallees' _ _                                 = []

procCalleesRec :: (?spec::Spec) => Scope -> Statement -> [MethodRef]
procCalleesRec s stat = ms1 ++ ms2
    where ms1 = procCallees' s stat
          ms2 = concatMap (procCalleesRec s . fromRight . methBody . snd . getMethod s) ms1

-- Find processes forked by the statement
forkedProcs :: (?spec::Spec) => Statement -> [(Ident, Statement)]
forkedProcs (SSeq _ ss)              = concatMap forkedProcs ss
forkedProcs (SPar _ ps)              = ps
forkedProcs (SForever _ b)           = forkedProcs b
forkedProcs (SDo _ b _)              = forkedProcs b
forkedProcs (SWhile _ _ b)           = forkedProcs b
forkedProcs (SFor _ (minit, c, i) b) = fromMaybe [] (fmap forkedProcs minit) ++ forkedProcs i ++ forkedProcs b
forkedProcs (SChoice _ ss)           = concatMap forkedProcs ss
forkedProcs (SITE _ _ t me)          = forkedProcs t ++ fromMaybe [] (fmap forkedProcs me)
forkedProcs (SCase _ _ cs mdef)      = concatMap (forkedProcs . snd) cs ++
                                       fromMaybe [] (fmap forkedProcs mdef)
forkedProcs _                        = []

-- Recurse over task invocations
forkedProcsRec :: (?spec::Spec) => Scope -> Statement -> [(Scope, (Ident, Statement))]
forkedProcsRec s stat = 
    (map (s,) $ forkedProcs stat) ++
    (concatMap (\m -> map (ScopeMethod tmMain m,) $ forkedProcs $ fromRight $ methBody m) (procCallees s stat))

---------------------------------------------------------------
-- CFA to LTS transformation
---------------------------------------------------------------

cfaToIProcess :: PID -> (I.CFA,[I.Var]) -> ProcTrans
cfaToIProcess pid (cfa,vs) = --trace ("cfaToIProcess\nCFA: " ++ show cfa ++ "\nreachable: " ++ (intercalate ", " $ map show r)) $
                             I.cfaTraceFileMany (map I.tranCFA trans') ("tran_" ++ pidToName pid) $
                             ProcTrans pid trans' vs final pcenum wait
    where
    -- compute a set of transitions for each location labelled with pause or final
    trans = concatMap (locTrans cfa . fst)
                      $ filter (I.isDelayLabel . snd)
                      $ G.labNodes cfa
    -- filter out unreachable transitions
    r = S.toList $ reachable $ S.singleton I.cfaInitLoc
    trans' = map (utranSuffix pid True False) $ filter (\t -> elem (I.tranFrom t) r) trans
    final = filter (\loc -> case I.cfaLocLabel loc cfa of
                                 I.LFinal -> True
                                 _        -> False) r
    pcenum = I.Enumeration (mkPCEnumName pid) $ map (mkPCEnum pid) r
    wait   = map (\loc -> case I.cfaLocLabel loc cfa of
                               I.LFinal      -> (loc, I.true)
                               I.LPause cond -> (loc, cond)) r

    reachable :: S.Set I.Loc -> S.Set I.Loc
    reachable locs = if S.null $ locs' S.\\ locs
                        then locs'
                        else reachable locs'
        where locs' = S.union locs (S.unions $ map suc $ S.toList locs)
    suc loc = S.fromList $ map I.tranTo $ filter ((==loc) . I.tranFrom) trans


locTrans :: I.CFA -> I.Loc -> [I.Transition]
locTrans cfa loc =
    let -- compute all reachable locations before pause
        r = reach cfa S.empty (S.singleton loc)
        -- construct subgraph with only these nodes
        cfa' = foldl' (\g l -> if l==loc || S.member l r then g else G.delNode l g) cfa (G.nodes cfa)
        -- check for loop freedom
        -- for each final location, compute a subgraph that connects the two
        dst = filter (I.isDelayLabel . fromJust . G.lab cfa) $ S.toList r 
    in --trace ("locTrans loc=" ++ show loc ++ " dst=" ++ show dst ++ " reach=" ++ show r) $
       map (\dst -> I.Transition loc dst $ pruneTrans cfa' loc dst) dst

-- locations reachable from found before reaching the next pause or final state
reach :: I.CFA -> S.Set I.Loc -> S.Set I.Loc -> S.Set I.Loc
reach cfa found frontier = if S.null frontier'
                              then found'
                              else reach cfa found' frontier'
    where new       = suc frontier
          found'    = S.union found new
          -- frontier' - all newly discovered states that are not pause or final states
          frontier' = S.filter (not . I.isDelayLabel . fromJust . G.lab cfa) $ new S.\\ found
          suc locs  = S.unions $ map suc1 (S.toList locs)
          suc1 loc  = S.fromList $ G.suc cfa loc

-- Insert constraints over PC and cont variables after the last location of 
-- the transition
utranSuffix :: PID -> Bool -> Bool -> I.Transition -> I.Transition
utranSuffix pid updatepc updatecont (I.Transition from to cfa) = 
    let -- If this is a loop transition, split the initial node
        (init, final, cfa1) = if from == to
                                 then splitLoc from cfa
                                 else (from, to, cfa)
        -- update PC if requested
        (cfa3, aftpc) = if updatepc
                           then let (cfa2, loc1) = I.cfaInsTrans' final (I.SAssume $ mkPCVar pid I.=== mkPC pid from) cfa1
                                in I.cfaInsTrans' loc1 (mkPCVar pid I.=: mkPC pid to) cfa2
                           else (cfa1, final)
        -- non-deterministically reset the cont to true if inside a magic block
        (cfa6,aftcont) = if updatecont 
                            then let (cfa4, loc3)    = I.cfaInsTrans' aftpc (I.SAssume $ mkMagicVar I.=== I.true) cfa3
                                     (cfa5, aftcont) = I.cfaInsTrans' loc3  (mkContVar I.=: I.false) cfa4
                                 in (I.cfaInsTrans aftpc aftcont I.nop cfa5, aftcont)
                  else (cfa3, aftpc)
        -- set $pid
        (cfa7, after)   = I.cfaInsTrans' aftcont (mkPIDVar I.=: mkPIDEnum pid) cfa6
    in I.Transition init after cfa7

tranAppend :: I.Transition -> I.Statement -> I.Transition
tranAppend (I.Transition from to cfa) s = I.Transition from to' cfa'
    where (cfa', to') = I.cfaInsTrans' to s cfa

-- Split location into 2, one containing all outgoing edges and one containing
-- all incoming edges of the original location
splitLoc :: I.Loc -> I.CFA -> (I.Loc, I.Loc, I.CFA)
splitLoc loc cfa = (loc, loc', cfa3)
    where i            = G.inn cfa loc
          cfa1         = foldl' (\cfa (f,t,_) -> G.delEdge (f,t) cfa) cfa i 
          (cfa2, loc') = I.cfaInsLoc I.LNone cfa1
          cfa3         = foldl' (\cfa (f,t,l) -> G.insEdge (f,loc',l) cfa) cfa2 i


-- iteratively prune dead-end locations until only transitions connecting from and to remain
pruneTrans :: I.CFA -> I.Loc -> I.Loc -> I.CFA
pruneTrans cfa from to = if G.noNodes cfa' == G.noNodes cfa then cfa else pruneTrans cfa' from to
    where cfa' = foldl' (\g loc -> if loc /= to && null (G.suc g loc) then G.delNode loc g else g) cfa (G.nodes cfa) 
