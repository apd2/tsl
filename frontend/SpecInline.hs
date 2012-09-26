{-# LANGUAGE ImplicitParams, TupleSections #-}

-- Convert flattened spec to internal representation
module SpecInline () where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State

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

-- Process structure analysis: subprocesses, methods, variables

---- Recursively compute the set of methods invoked by the statement.
---- (assume that the spec has been simplified previously)
--statMethods :: (?spec::Spec, ?scope::Scope) => Statement -> [Ident]
--statMethods (SReturn _ (Just (EApply _ mref _))) = mrefMethods mref
--statMethods (SSeq    _ ss)                       = concatMap statMethods ss
--statMethods (SForever _ s)                       = statMethods s
--statMethods (SDo _ b c)                          = statMethods b
--statMethods (SWhile _ c b)                       = statMethods b
--statMethods (SFor  _ (mi,c,s) b)                 = nub $ concatMap statMethods $ (maybeToList mi) ++ [s,b]
--statMethods (SChoice _ ss)                       = nub $ concatMap statMethods ss
--statMethods (SInvoke _ mref _)                   = mrefMethods mref
--statMethods (SAssign _ lhs (EApply _ mref _))    = mrefMethods mref
--statMethods (SITE _ _ t me)                      = nub $ concatMap statMethods $ t : (maybeToList me)
--statMethods (SCase _ _ cs mdef)                  = nub $ concatMap statMethods $ (snd $ unzip cs) ++ (maybeToList mdef)
--statMethods _                                    = []
--
--mrefMethods :: (?spec::Spec, ?scope::Scope) => MethodRef -> [Ident]
--mrefMethods mref = 
--    let m = snd $ getMethod ?scope mref
--    in let ?scope = ScopeMethod tmMain m 
--       in nub $ (name m):(statMethods $ fromRight $ methBody m)

-- Child processes spawned by the statement (including processes spawned 
-- by tasks invoked by the statement)
--procChildren :: (?spec::Spec, ?scope::Scope) => Statement -> [(Ident, Scope, Statement)]
--procChildren st = map (\(n, st) -> (n,?scope,st)) (statSubprocessNonrec st) ++
--                  concatMap (\(tm',m) -> map (\(n,st) -> (n, ScopeMethod tm' m, st)) $ statSubprocessNonrec $ fromRight $ methBody m) ms
--    where ms = map (getMethod (ScopeTemplate tmMain) . (\n -> MethodRef (pos n) [n])) $ statMethods st


----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------

specIVars :: (?spec::Spec) => ([I.Var], I.Enumeration)
specIVars = (mkMagicVarDecl : tvar : (gvars ++ fvars ++ cvars ++ tvars ++ pvars), tenum)
    where
    -- tag: one enumerator per controllable task
    (tvar, tenum) = mkTagVarDecl

    -- global variables
    gvars = let ?scope = ScopeTemplate tmMain in map (mkVarDecl Nothing Nothing . gvarVar) $ tmVar tmMain

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
procToCFA :: (?spec::Spec, ?procs::[I.Process]) => PID -> Process -> I.CFA
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
fprocToCFA :: (?spec::Spec, ?procs::[I.Process]) => PID -> NameMap -> Scope -> Statement -> I.CFA
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
taskToCFA :: (?spec::Spec, ?procs::[I.Process]) => PID -> Method -> Bool -> I.CFA
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

--spec2Internal :: Spec -> I.Spec
--spec2Internal s = I.Spec senum svar sproc sctl sinvis sinit sgoal
--    where ?spec = specSimplify s -- preprocessing
--          senum = mapMaybe (\d -> case tspec d of
--                                     EnumSpec _ es -> I.Enum (sname d) (map sname es)
--                                     _             -> Nothing) (specType ?spec)
--          sproc = (concatMap procTree (specProcess ?spec)) ++ 
--                  concatMap (filter ((== Task Controllable) . methCat m) $ tmMethod tmMain)
--          -- TODO: controllable processes
--          { specEnum         :: [Enumeration]
--          , specVar          :: [Var]
--          , specProcess      :: [Process]
--          , specInit         :: Process
--          , specGoal         :: [Goal] 
--          }


-- Recursively construct LTS for the process and its children
procTree :: (?spec::Spec) => Process -> [I.Process]
procTree p = 
    let pid      = [sname p]
        scope    = ScopeProcess tmMain p
        children = procTreeRec pid scope (procStatement p) (procLMap pid p)
        iproc    = let ?procs = children in cfaToIProcess (pidToName pid) $ procToCFA pid p
    in iproc : children

fprocTree :: (?spec::Spec) => PID -> Scope -> NameMap -> (Ident, Statement) -> [I.Process]
fprocTree parpid parscope lmap (n,stat) = 
    let pid      = parpid ++ [sname n]
        children = procTreeRec pid parscope stat lmap
        iproc    = let ?procs = children in cfaToIProcess (pidToName pid) $ fprocToCFA pid lmap parscope stat
    in iproc : children

taskProcTree :: (?spec::Spec) => PID -> Method -> [I.Process]
taskProcTree parpid meth = 
    let pid      = parpid ++ [sname meth]
        children = procTreeRec parpid (ScopeMethod tmMain meth) (fromRight $ methBody meth) (methodLMap parpid meth)
        iproc    = let ?procs = children in cfaToIProcess (pidToName pid) $ taskToCFA parpid meth False
    in iproc : children

-- Recursive step of the algorithm: find all child subprocesses of a statement
procTreeRec :: (?spec::Spec) => PID -> Scope -> Statement -> NameMap -> [I.Process]
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

cfaToIProcess :: String -> I.CFA -> I.Process
cfaToIProcess n cfa = I.Process n trans final
    where
    -- compute a set of transitions for each location labelled with pause or final
    trans = concatMap (locTrans cfa . fst)
                      $ filter (\(_, lab) -> lab == LPause || lab == LFinal)
                      $ labNodes cfa

locTrans :: I.CFA -> I.Loc -> [I.Transition]
locTrans cfa loc =
    -- compute all reachable locations before pause
    -- check for loop freedom
    -- for each final location, compute a subgraph that connects the two by iteratively pruning dead-end locations


