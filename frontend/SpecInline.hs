{-# LANGUAGE ImplicitParams, TupleSections #-}

-- Convert flattened spec to internal representation
module SpecInline () where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import qualified Data.Graph.Inductive.Graph as G

import Util hiding (name)
import TSLUtil
import Spec
import qualified ISpec as I
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
import Var
import Method
import Process
import Type
import TypeOps
import Inline

-- Preprocess all statements and expressions before inlining.  
-- In the preprocessed spec:
-- * Method calls can only appear in top-level expressions
-- * No method calls in return statements
-- * Local variables are declared and initialised separately

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

spec2Internal :: Spec -> I.Spec
spec2Internal s = 
    let ?spec = specSimplify s -- preprocessing
    in let senum = mapMaybe (\d -> case tspec d of
                                        EnumSpec _ es -> Just $ I.Enumeration (sname d) (map sname es)
                                        _             -> Nothing) (specType ?spec)
           (vars, tagenum) = mkVars
           -- Controllable transitions
           ctran = mkMagicReturn : (map mkCTran $ filter ((== Task Controllable) . methCat) $ (tmMethod tmMain))
           -- Uncontrollable processes
           uproc = concatMap procTree $ tmProcess tmMain
           cproc = map (\m -> let ?procs = [] in cfaToIProcess [sname m] $ taskToCFA [] m True) 
                       $ filter ((== Task Controllable) . methCat)
                       $ tmMethod tmMain
           -- PC variables and enums
           (pcvars, pcenums) = unzip $ map (\p -> let enum = pPCEnum p
                                                      var  = I.Var (mkPCVarName $ pPID p) (I.Enum $ I.enumName enum)
                                                  in  (var, enum)) uproc
           -- Uncontrollable transitions
           utran = concatMap pBody uproc
       in I.Spec (tagenum : (senum ++ pcenums))
                 (vars ++ pcvars) 
                 ctran
                 utran
                 mkWires
                 mkInit
                 (map mkGoal (tmGoal tmMain))

----------------------------------------------------------------------
-- Wires
----------------------------------------------------------------------

mkWires :: (?spec::Spec) => I.Transition
mkWires = 
    let wires = orderWires
        -- Generate assignment statement for each wire
        stat = let ?scope = ScopeTemplate tmMain
                   ?uniq  = newUniq
               in statSimplify $ SSeq nopos $ map (\w -> SAssign nopos (ETerm nopos [name w]) (fromJust $ wireRHS w)) wires
        ctx = CFACtx { ctxPID    = []
                     , ctxScope  = ScopeTemplate tmMain
                     , ctxCFA    = I.newCFA
                     , ctxRetLoc = error "return from a wire assignment"
                     , ctxBrkLoc = error "break outside a loop"
                     , ctxLHS    = Nothing
                     , ctxGNMap  = globalNMap
                     , ctxLNMap  = M.empty}
        proc = let ?procs = [] in cfaToIProcess [] $ ctxCFA $ execState (statToCFA I.cfaInitLoc stat) ctx
    in case pBody proc of
            [t] -> t
            _   -> error "mkWires: Invalid wire expression"


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
-- Init and goal conditions
----------------------------------------------------------------------

mkInit :: (?spec::Spec) => I.Expr
mkInit = mkCond cond
    where -- conjunction of initial variable assignments
          ass = mapMaybe (\v -> case varInit $ gvarVar v of
                                     Nothing -> Nothing
                                     Just e  -> Just (EBinOp (pos v) Eq (ETerm nopos $ [name v]) e)) (tmVar tmMain)
          -- add init blocks
          cond = eAnd nopos (ass ++ map initBody (tmInit tmMain))
       
mkGoal :: (?spec::Spec) => Goal -> I.Goal
mkGoal g = I.Goal (sname g) (mkCond $ goalCond g)


mkCond :: (?spec::Spec) => Expr -> I.Expr
mkCond e = 
    let -- simplify and convert into a statement
        (ss, cond') = let ?scope = ScopeTemplate tmMain 
                          ?uniq = newUniq
                      in exprSimplify e
        stat = SSeq nopos (ss ++ [SAssume nopos cond'])
        iproc = let ?procs = [] in cfaToIProcess [] $ fprocToCFA [] M.empty (ScopeTemplate tmMain) stat
        -- precondition
        pre = case pBody iproc of
                   [t] -> I.wp I.true [t]
                   _   -> error "mkCond: Invalid init block"
    in  -- make sure that precondition only depends on state variables
        case filter I.isTmpVar $ I.exprVars pre of
             [] -> pre
             _  -> error "mkCond: tmp variable in precondition"


----------------------------------------------------------------------
-- Controllable transitions
----------------------------------------------------------------------

-- only allow controllable transitions when inside a magic block and in
-- a controllable state
contGuard = I.SAssume $ I.conj $ [mkMagicVar I.=== I.true, mkContVar I.=== I.true]

mkCTran :: (?spec::Spec) => Method -> I.Transition
mkCTran m = I.Transition I.cfaInitLoc after cfa2
    where (cfa0, aftguard) = I.cfaInsTrans' I.cfaInitLoc contGuard I.newCFA
          (cfa1, aftargs)  = foldl' (\(cfa,loc) arg -> I.cfaInsTrans' loc (mkVar Nothing (Just m) arg I.=: I.ENonDet) cfa)
                                    (cfa0, aftguard) $ filter ((==ArgIn) . argDir) (methArg m)
          -- switch to uncontrollable state
          (cfa2, after)    = I.cfaInsTrans' aftargs (mkContVar I.=: I.false) cfa1

mkMagicReturn :: (?spec::Spec) => I.Transition
mkMagicReturn = I.Transition I.cfaInitLoc after cfa2
    where (cfa0, aftguard) = I.cfaInsTrans' I.cfaInitLoc contGuard               I.newCFA
          (cfa1, aftmagic) = I.cfaInsTrans' aftguard   (mkMagicVar I.=: I.false) cfa0
          (cfa2, after)    = I.cfaInsTrans' aftmagic   (mkContVar I.=: I.false)  cfa1

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------

mkVars :: (?spec::Spec) => ([I.Var], I.Enumeration)
mkVars = (mkContVarDecl : mkMagicVarDecl : tvar : (wires ++ gvars ++ fvars ++ cvars ++ tvars ++ pvars), tenum)
    where
    -- tag: one enumerator per controllable task
    (tvar, tenum) = mkTagVarDecl

    -- global variables
    gvars = let ?scope = ScopeTemplate tmMain in map (mkVarDecl Nothing Nothing . gvarVar) $ tmVar tmMain

    -- wires
    wires = let ?scope = ScopeTemplate tmMain in map (mkVarDecl Nothing Nothing) $ tmWire tmMain

    -- local variables and input arguments of functions and procedures
    fvars = concatMap (\m -> (let ?scope = ScopeMethod tmMain m in map (mkVarDecl Nothing (Just m)) (methVar m)) ++
                             (let ?scope = ScopeTemplate tmMain in map (mkVarDecl Nothing (Just m)) 
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
    -- * PC variable
    tvars = concatMap (concat . mapPTreeTask (\pid m -> (mkEnVarDecl pid (Just m)) : (taskVars (Just pid) m)))
                      $ tmProcess tmMain

    -- For each forked process:
    -- * enabling variable
    pvars = concatMap (mapPTreeProc (\pid _ -> mkEnVarDecl pid Nothing))
                      $ tmProcess tmMain

    taskVars :: Maybe PID -> Method -> [I.Var]
    taskVars mpid m = 
        (let ?scope = ScopeTemplate tmMain in map (mkVarDecl mpid (Just m)) (methVar m)) ++ 
        (let ?scope = ScopeMethod tmMain m in map (mkVarDecl mpid (Just m)) (methArg m)) ++
        maybeToList (mkRetVarDecl mpid m)

----------------------------------------------------------------------
-- CFA transformation
----------------------------------------------------------------------

-- Convert process to CFA
-- For a forked process the mparpid argument is the PID of the process in 
-- whose syntactic scope the present process is located.
procToCFA :: (?spec::Spec, ?procs::[ProcTrans]) => PID -> Process -> I.CFA
procToCFA pid proc = ctxCFA ctx'
    where ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = ScopeProcess tmMain proc
                       , ctxCFA    = I.newCFA
                       , ctxRetLoc = error "return from a process"
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = Nothing
                       , ctxGNMap  = globalNMap
                       , ctxLNMap  = procLMap pid proc}
          ctx' = execState (statToCFA I.cfaInitLoc (procStatement proc)) ctx

-- Convert forked process to CFA
fprocToCFA :: (?spec::Spec, ?procs::[ProcTrans]) => PID -> NameMap -> Scope -> Statement -> I.CFA
fprocToCFA pid lmap parscope stat = ctxCFA ctx'
    where -- Add process-local variables to nmap
          ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = parscope
                       , ctxCFA    = I.newCFA
                       , ctxRetLoc = error "return from a forked process"
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = Nothing
                       , ctxGNMap  = globalNMap
                       , ctxLNMap  = lmap}
          ctx' = execState (statToCFA I.cfaInitLoc stat) ctx

-- Convert controllable or uncontrollable task to CFA.
-- The ctl argument indicates that a controllable transition is to be
-- generated (using tag instead of enabling variable)
taskToCFA :: (?spec::Spec, ?procs::[ProcTrans]) => PID -> Method -> Bool -> I.CFA
taskToCFA pid meth ctl = ctxCFA ctx'
    where stat = fromRight $ methBody meth
          ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = ScopeMethod tmMain meth
                       , ctxCFA    = I.newCFA
                       , ctxRetLoc = I.cfaInitLoc
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = mkRetVar (Just pid) meth
                       , ctxGNMap  = globalNMap
                       , ctxLNMap  = methodLMap pid meth}
          ctx' = if ctl
                    then execState (do aftwait <- ctxInsTrans' I.cfaInitLoc $ I.SAssume $ mkTagVar I.=== tagMethod meth
                                       aftbody <- statToCFA aftwait stat
                                       ctxInsTrans aftbody I.cfaInitLoc $ mkTagVar I.=: tagIdle) 
                                   ctx
                    else execState (do aftwait <- ctxInsTrans' I.cfaInitLoc $ I.SAssume $ mkEnVar pid (Just meth) I.=== I.true
                                       aftbody <- statToCFA aftwait stat
                                       ctxInsTrans aftbody I.cfaInitLoc $ (mkEnVar pid (Just meth)) I.=: I.false) 
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

-- Map a function over process and its subprocesses
mapPTreeProc :: (?spec::Spec) => (PID -> Statement -> a) -> Process -> [a]
mapPTreeProc f p = mapPTreeProc' f [sname p] (ScopeProcess tmMain p) (procStatement p)

mapPTreeProc' :: (?spec::Spec) => (PID -> Statement -> a) -> PID -> Scope -> Statement -> [a]
mapPTreeProc' f pid s stat = 
    f pid stat :
    (concatMap (\(s',(n,st)) -> mapPTreeProc' f (pid++[sname n]) s' st) $ forkedProcsRec s stat)


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

cfaToIProcess :: PID -> I.CFA -> ProcTrans
cfaToIProcess pid cfa = ProcTrans pid trans' final pcenum
    where
    -- compute a set of transitions for each location labelled with pause or final
    trans = concatMap (locTrans cfa . fst)
                      $ filter (\(_, lab) -> lab == I.LPause || lab == I.LFinal)
                      $ G.labNodes cfa
    -- filter out unreachable transitions
    r = reachable $ S.singleton I.cfaInitLoc
    trans' = map (utranSuffix pid) $ filter (\t -> S.member (I.tranFrom t) r) trans
    final = filter (\loc -> I.cfaLocLabel loc cfa == I.LFinal) $ S.toList r
    pcenum = I.Enumeration (mkPCEnumName pid) $ map (mkPCEnum pid) $ S.toList r

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
        cfa' = foldl' (\g loc -> if S.member loc r then g else G.delNode loc g) cfa (G.nodes cfa)
        -- check for loop freedom
        -- for each final location, compute a subgraph that connects the two
        dst = filter (\loc -> elem (G.lab cfa loc) [Just I.LPause, Just I.LFinal]) $ S.toList r 
    in map (\dst -> I.Transition loc dst $ pruneTrans cfa' loc dst) dst
    
-- Insert constraints over PC and cont variables after the last location of 
-- the transition
utranSuffix :: PID -> I.Transition -> I.Transition
utranSuffix pid (I.Transition from to cfa) = 
    let -- If this is a loop transition, split the initial node
        (init, final, cfa1) = if from == to
                                 then splitLoc from cfa
                                 else (from, to, cfa)
        (cfa2, loc1)  = I.cfaInsTrans' final (I.SAssume $ mkPCVar pid I.=== mkPC pid from) cfa1
        (cfa3, aftpc) = I.cfaInsTrans' loc1  (mkPCVar pid I.=: mkPC pid to)                cfa2
        -- if tag==idle && magic==true, non-deterministically set cont:=true
        (cfa4, loc3)  = I.cfaInsTrans' aftpc (I.SAssume $ I.conj [mkTagVar I.=== tagIdle, mkMagicVar I.=== I.true]) cfa3
        (cfa5, after) = I.cfaInsTrans' loc3  (mkContVar I.=: I.false)                      cfa4
        cfa6          = I.cfaInsTrans  aftpc after I.nop                                   cfa5
    in I.Transition init after cfa6

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
    
-- locations reachable from found before reaching the next pause or final state
reach :: I.CFA -> S.Set I.Loc -> S.Set I.Loc -> S.Set I.Loc
reach cfa found frontier = if S.null frontier'
                              then found
                              else reach cfa found' frontier'
    where new       = suc frontier
          found'    = S.union found new
          -- frontier' - all newly discovered states that are not pause or final states
          frontier' = S.filter (\loc -> notElem (G.lab cfa loc) [Just I.LPause, Just I.LFinal]) $ new S.\\ found
          suc locs  = S.unions $ map suc1 (S.toList locs)
          suc1 loc  = S.fromList $ G.suc cfa loc
