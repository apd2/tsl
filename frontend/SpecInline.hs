{-# LANGUAGE ImplicitParams #-}

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
import Template
import Var
import Method
import Process
import Type
import TypeOps

-- Extract template from flattened spec (that only has one template)
tmMain :: (?spec::Spec) => Template
tmMain = head $ specTemplate ?spec

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

-- Recursively compute the set of methods invoked by the statement.
-- (assume that the spec has been simplified previously)
statMethods :: (?spec::Spec, ?scope::Scope) => Statement -> [Ident]
statMethods (SReturn _ (Just (EApply _ mref _))) = mrefMethods mref
statMethods (SSeq    _ ss)                       = concatMap statMethods ss
statMethods (SForever _ s)                       = statMethods s
statMethods (SDo _ b c)                          = statMethods b
statMethods (SWhile _ c b)                       = statMethods b
statMethods (SFor  _ (mi,c,s) b)                 = nub $ concatMap statMethods $ (maybeToList mi) ++ [s,b]
statMethods (SChoice _ ss)                       = nub $ concatMap statMethods ss
statMethods (SInvoke _ mref _)                   = mrefMethods mref
statMethods (SAssign _ lhs (EApply _ mref _))    = mrefMethods mref
statMethods (SITE _ _ t me)                      = nub $ concatMap statMethods $ t : (maybeToList me)
statMethods (SCase _ _ cs mdef)                  = nub $ concatMap statMethods $ (snd $ unzip cs) ++ (maybeToList mdef)
statMethods _                                    = []

mrefMethods :: (?spec::Spec, ?scope::Scope) => MethodRef -> [Ident]
mrefMethods mref = 
    let m = snd $ getMethod ?scope mref
    in let ?scope = ScopeMethod tmMain m 
       in nub $ (name m):(statMethods $ fromRight $ methBody m)

-- Child processes spawned by the statement (including processes spawned 
-- by tasks invoked by the statement)
procChildren :: (?spec::Spec, ?scope::Scope) => Statement -> [(Ident, Scope, Statement)]
procChildren st = map (\(n, st) -> (n,?scope,st)) (statSubprocessNonrec st) ++
                  concatMap (\(tm',m) -> map (\(n,st) -> (n, ScopeMethod tm' m, st)) $ statSubprocessNonrec $ fromRight $ methBody m) ms
    where ms = map (getMethod (ScopeTemplate tmMain) . (\n -> MethodRef (pos n) [n])) $ statMethods st


----------------------------------------------------------------------
-- Process ID (path in the process tree)
----------------------------------------------------------------------

type PID = [String]

-- PID to process name
pidToName :: PID -> String
pidToName pid = intercalate "/" pid

childPID :: PID -> Ident -> PID
childPID pid pname = pid ++ [sname pname]

----------------------------------------------------------------------
-- Names
----------------------------------------------------------------------

initid = [":init"]

globaliseName :: (WithName a) => PID -> a -> String
globaliseName pid x = intercalate "/" $ (pid ++ [sname x])

globaliseVar :: (WithName a) => PID -> Method -> a -> I.Expr
globaliseVar pid meth x = globaliseVarS pid meth (sname x)

globaliseVarS :: PID -> Method -> String -> I.Expr
globaliseVarS pid meth n = I.EVar $ intercalate "/" $ (pid ++ [sname meth,n])

-- Variable that stores return value of a task
retIVar :: PID -> Method -> Maybe I.Expr
retIVar pid meth = case methRettyp meth of
                        Nothing -> Nothing
                        Just _  -> Just $ globaliseVarS pid meth "$ret"

enableIVar :: PID -> Method -> I.Expr
enableIVar pid meth = globaliseVarS pid meth "$en"


-- Variable used to make a forked process runnable
--runIVarName :: PID -> String
--runIVarName pid = globaliseName pid (Ident nopos "$run")


----------------------------------------------------------------------
-- Convert expressions to internal format
----------------------------------------------------------------------

exprToIExpr :: (?spec::Spec) => Expr -> State CFACtx I.Expr
exprToIExpr (ETerm _ ssym) = do
    scope <- gets ctxScope
    lmap  <- gets ctxLNMap
    gmap  <- gets ctxGNMap
    let n = case getTerm scope ssym of
                 ObjVar      _ v -> name v
                 ObjGVar     _ v -> name v
                 ObjWire     _ w -> name w
                 ObjArg      _ a -> name a
                 ObjConst    _ c -> name c
                 ObjEnum     _ e -> name e
    return $ case M.lookup n gmap of
                  Just e -> e
                  Nothing -> case M.lookup n lmap of
                                  Just e  -> e
                                  Nothing -> error $ "exprToIExpr: unknown name: " ++ sname n

exprToIExpr (ELit _ _ _ _ v)             = return $ I.EConst $ I.IntVal v
exprToIExpr (EBool _ b)                  = return $ I.EConst $ I.BoolVal b
exprToIExpr (EField _ e f)               = do e' <- exprToIExpr e
                                              return $ I.EField e' (sname f)
exprToIExpr (EPField _ e f)              = do e' <- exprToIExpr e
                                              let e'' = I.EUnOp Deref e'
                                              return $ I.EField e'' (sname f)
exprToIExpr (EIndex _ e i)               = do e' <- exprToIExpr e
                                              i' <- exprToIExpr i
                                              return $ I.EIndex e' i'
exprToIExpr (EUnOp _ op e)               = do e' <- exprToIExpr e
                                              return $ I.EUnOp op e'
exprToIExpr (EBinOp _ op e1 e2)          = do e1' <- exprToIExpr e1
                                              e2' <- exprToIExpr e2
                                              return $ I.EBinOp op e1' e2'
exprToIExpr (ESlice _ e (l,h))           = do scope <- gets ctxScope
                                              let ?scope = scope
                                              e' <- exprToIExpr e
                                              let l' = fromInteger $ evalInt l
                                                  h' = fromInteger $ evalInt h
                                              return $ I.ESlice e' (l',h')
exprToIExpr e@(EStruct _ tname (Left fs))= do scope <- gets ctxScope
                                              let ?scope = scope
                                              let StructSpec _ sfs = tspec $ typ' e
                                              fs' <- mapM (exprToIExpr . snd . fromJust . (\f -> find ((==f) . fst) fs) . name) sfs
                                              return $ I.EStruct (sname $ head tname) fs'
exprToIExpr (EStruct _ tname (Right fs)) = do fs' <- mapM exprToIExpr fs
                                              return $ I.EStruct (sname $ head tname) fs'


exprToIExpr (ENonDet _)                  = return I.ENonDet


----------------------------------------------------------------------
-- CFA transformation
----------------------------------------------------------------------


type NameMap = M.Map Ident I.Expr

methodLMap :: PID -> Method -> NameMap 
methodLMap pid meth = 
    M.fromList $ map (\v -> (name v, globaliseVar pid meth v)) (methVar meth) ++
                 map (\a -> (name a, globaliseVar pid meth a)) (methArg meth)

procLMap :: PID -> Process -> NameMap
procLMap pid p = M.fromList $ map (\v -> (name v, I.EVar $ globaliseName pid v)) (procVar p)

globalNMap :: (?spec::Spec) => NameMap
globalNMap = error $ "Not implemented: globalNMap"


-- State maintained during CFA construction
data CFACtx = CFACtx { ctxPID    :: PID           -- PID of the process being constructed
                     , ctxScope  :: Scope         -- current syntactic scope
                     , ctxCFA    :: I.CFA         -- CFA constructed so far
                     , ctxRetLoc :: I.Loc         -- return location
                     , ctxBrkLoc :: I.Loc         -- break location
                     , ctxLHS    :: Maybe I.Expr  -- LHS expression
                     , ctxGNMap  :: NameMap       -- global variable visible in current scope
                     , ctxLNMap  :: NameMap       -- local variable map
                     }

ctxInsLoc :: State CFACtx I.Loc
ctxInsLoc = do
    ctx <- get
    let (cfa', loc) = I.cfaInsLoc $ ctxCFA ctx
    put $ ctx {ctxCFA = cfa'}
    return loc

ctxInsTrans :: I.Loc -> I.Loc -> I.Statement -> State CFACtx ()
ctxInsTrans from to stat = modify $ (\ctx -> ctx {ctxCFA = I.cfaInsTrans from to stat $ ctxCFA ctx})

ctxInsTrans' :: I.Loc -> I.Statement -> State CFACtx I.Loc
ctxInsTrans' from stat = do
    to <- ctxInsLoc
    ctxInsTrans from to stat
    return to

ctxPutBrkLoc :: I.Loc -> State CFACtx ()
ctxPutBrkLoc loc = modify $ (\ctx -> ctx {ctxBrkLoc = loc})

ctxPutRetLoc :: I.Loc -> State CFACtx ()
ctxPutRetLoc loc = modify $ (\ctx -> ctx {ctxRetLoc = loc})

ctxPutLNMap :: NameMap -> State CFACtx ()
ctxPutLNMap m = modify $ (\ctx -> ctx {ctxLNMap = m})

ctxPutLHS :: Maybe I.Expr -> State CFACtx ()
ctxPutLHS lhs = modify $ (\ctx -> ctx {ctxLHS = lhs})

ctxPutScope :: Scope -> State CFACtx ()
ctxPutScope s = modify $ (\ctx -> ctx {ctxScope = s})


-- Convert process to CFA
-- For a forked process the mparpid argument is the PID of the process in 
-- whose syntactic scope the present process is located.
procToCFA :: (?spec::Spec) => PID -> Process -> I.CFA
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
fprocToCFA :: (?spec::Spec) => PID -> NameMap -> Scope -> Statement -> I.CFA
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

-- Convert controllable or uncontrollable task to CFA
taskToCFA :: (?spec::Spec) => PID -> Method -> I.CFA
taskToCFA pid meth = ctxCFA ctx'
    where stat = fromRight $ methBody meth
          ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = ScopeMethod tmMain meth
                       , ctxCFA    = I.newCFA
                       , ctxRetLoc = I.cfaInitLoc
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = retIVar pid meth
                       , ctxGNMap  = globalNMap
                       , ctxLNMap  = methodLMap pid meth}
          ctx' = execState (do aftwait <- ctxInsTrans' I.cfaInitLoc $ I.SAssume $ enableIVar pid meth I.=== I.true
                               aftbody <- statToCFA aftwait stat
                               ctxInsTrans aftbody I.cfaInitLoc $ (enableIVar pid meth) I.=: I.false) 
                           ctx

-- Convert process statement to CFA
statToCFA :: (?spec::Spec) => I.Loc -> Statement -> State CFACtx I.Loc
statToCFA before (SSeq _ ss) = foldM statToCFA before ss
statToCFA before stat = do
    after <- ctxInsLoc
    statToCFA' before after stat
    return after

-- Only safe to call from statToCFA.  Do not call this function directly!
statToCFA' :: (?spec::Spec) => I.Loc -> I.Loc -> Statement -> State CFACtx ()
statToCFA' before after (SVarDecl _ _) = ctxInsTrans before after I.SNop
statToCFA' before after (SReturn _ rval) = do
    -- add transition before before to return location
    lhs <- gets ctxLHS
    ret <- gets ctxRetLoc
    stat <- case rval of 
                 Nothing -> return I.SNop
                 Just v  -> case lhs of
                                 Nothing  -> return I.SNop
                                 Just lhs -> do vi <- exprToIExpr v
                                                return $ lhs I.=: vi
    ctxInsTrans before ret stat

statToCFA' before after (SPar _ ps) = do
    pid <- gets ctxPID
    -- child process names
    let procs = map (pidToName . childPID pid . fst) ps
    ctxInsTrans before after (I.SFork procs)

statToCFA' before after (SForever _ stat) = do
    brkLoc <- gets ctxBrkLoc
    ctxPutBrkLoc after
    -- loc' = end of loop body
    loc' <- statToCFA before stat 
    -- loop-back transition
    ctxInsTrans loc' after I.SNop
    ctxPutBrkLoc brkLoc

statToCFA' before after (SDo _ stat cond) = do
    brkLoc <- gets ctxBrkLoc
    cond' <- exprToIExpr cond
    ctxInsTrans before after (I.SAssume $ I.EUnOp Not cond')
    -- after condition has been checked, before the body
    befbody <- ctxInsTrans' before (I.SAssume cond')
    -- body
    ctxPutBrkLoc after
    aftbody <- statToCFA befbody stat
    -- loop-back transition
    ctxInsTrans aftbody before I.SNop
    ctxPutBrkLoc brkLoc

statToCFA' before after (SWhile _ cond stat) = do
    brkLoc <- gets ctxBrkLoc
    cond' <- exprToIExpr cond
    ctxPutBrkLoc after
    aftbody <- statToCFA before stat
    ctxPutBrkLoc brkLoc
    -- loop-back transition
    ctxInsTrans aftbody before (I.SAssume cond')
    -- exit loop transition
    ctxInsTrans aftbody after (I.SAssume $ I.EUnOp Not cond')

statToCFA' before after (SFor _ (minit, cond, inc) body) = do
    brkLoc <- gets ctxBrkLoc
    cond' <- exprToIExpr cond
    aftinit <- case minit of
                    Nothing   -> return before
                    Just init -> statToCFA before init
    ctxInsTrans aftinit after (I.SAssume $ I.EUnOp Not cond')
    -- before loop body
    befbody <- ctxInsTrans' aftinit $ I.SAssume cond'
    ctxPutBrkLoc after
    aftbody <- statToCFA befbody body
    -- after increment is performed at the end of loop iteration
    aftinc <- statToCFA aftbody inc
    ctxPutBrkLoc brkLoc
    -- loopback transition
    ctxInsTrans aftinc befbody I.SNop

statToCFA' before after (SChoice _ ss) = do
    mapM (\s -> do aft <- statToCFA before s
                   ctxInsTrans aft after I.SNop) ss
    return ()

statToCFA' before after (SPause _) = ctxInsTrans before after I.SPause

statToCFA' before after (SStop _) = ctxInsTrans before after I.SStop

statToCFA' before after (SBreak _) = do
    brkLoc <- gets ctxBrkLoc
    ctxInsTrans before brkLoc I.SNop

statToCFA' before after (SInvoke _ mref as) = do
    scope <- gets ctxScope
    let meth = snd $ getMethod scope mref
    case methCat meth of
         Task Controllable   -> taskCall before after meth as Nothing
         Task Uncontrollable -> taskCall before after meth as Nothing
         _                   -> methInline before after meth as Nothing

statToCFA' before after (SAssert _ cond) = do
    cond' <- exprToIExpr cond
    ctxInsTrans before after (I.SAssume cond')
    ctxInsTrans before I.cfaErrLoc (I.SAssume $ I.EUnOp Not cond')

statToCFA' before after (SAssume _ cond) = do
    cond' <- exprToIExpr cond
    ctxInsTrans before after (I.SAssume cond')

statToCFA' before after (SAssign _ lhs (EApply _ mref args)) = do
    scope <- gets ctxScope
    let meth = snd $ getMethod scope mref
    case methCat meth of
         Task Controllable   -> taskCall before after meth args (Just lhs)
         Task Uncontrollable -> taskCall before after meth args (Just lhs)
         _                   -> methInline before after meth args (Just lhs)

statToCFA' before after (SAssign _ lhs rhs) = do
    lhs' <- exprToIExpr lhs
    rhs' <- exprToIExpr rhs
    ctxInsTrans before after $ lhs' I.=: rhs'

statToCFA' before after (SITE _ cond sthen mselse) = do
    befthen <- statToCFA before (SAssume nopos cond)
    aftthen <- statToCFA befthen sthen
    ctxInsTrans aftthen after I.SNop
    case mselse of
         Nothing -> return ()
         Just selse -> do befelse <- statToCFA before (SAssume nopos $ EUnOp nopos Not cond)
                          aftelse <- statToCFA befelse selse
                          ctxInsTrans aftelse after I.SNop

statToCFA' before after (SCase _ e cs mdef) = do
    let negs = map (eAnd nopos . map (EBinOp nopos Neq e)) $ inits $ map fst cs
        cs' = map (\((c, st), neg) -> (EBinOp nopos And (EBinOp nopos Eq e c) neg, st)) $ zip cs negs
        cs'' = case mdef of
                    Nothing  -> cs'
                    Just def -> cs' ++ [(last negs, def)]
    mapM (\(c,st) -> do befst <- statToCFA before (SAssume nopos c)
                        aftst <- statToCFA befst  st
                        ctxInsTrans aftst after I.SNop) cs''
    return ()


statToCFA' before after (SMagic _ (Left gname)) = do
    ctxInsTrans before after (I.SMagic $ Left $ sname gname)
  
statToCFA' before after (SMagic _ (Right g)) = do
    g' <- exprToIExpr g
    ctxInsTrans before after (I.SMagic $ Right g')

methInline :: (?spec::Spec) => I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> State CFACtx ()
methInline before after meth args mlhs = do
    -- save current context
    befctx <- get
    let pid = ctxPID befctx
    args' <- mapM exprToIExpr args
    lhs <- case mlhs of
                Nothing  -> return Nothing
                Just lhs -> (liftM Just) $ exprToIExpr lhs
    -- set input arguments
    aftarg <- setArgs before meth args'
    -- set return location
    retloc <- ctxInsLoc
    ctxPutRetLoc retloc
    -- clear break location
    ctxPutBrkLoc $ error "break outside a loop"
    -- change syntactic scope
    ctxPutScope $ ScopeMethod tmMain meth
    -- set LHS
    ctxPutLHS lhs
    -- build local map consisting of method arguments and local variables
    ctxPutLNMap $ methodLMap pid meth
    -- build CFA of the method
    aftbody <- statToCFA aftarg (fromRight $ methBody meth)
    ctxInsTrans aftbody retloc I.SNop

    -- copy out arguments
    aftout <- copyOutArgs retloc meth args'
    -- nop-transition to after
    ctxInsTrans aftout after I.SNop
    -- restore context
    ctxPutBrkLoc $ ctxBrkLoc befctx
    ctxPutRetLoc $ ctxRetLoc befctx
    ctxPutLNMap  $ ctxLNMap  befctx
    ctxPutLHS    $ ctxLHS    befctx


taskCall :: (?spec::Spec) => I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> State CFACtx ()
taskCall before after meth args mlhs = do
    pid <- gets ctxPID
    args' <- mapM exprToIExpr args
    lhs <- case mlhs of
                Nothing  -> return Nothing
                Just lhs -> (liftM Just) $ exprToIExpr lhs
    let envar = enableIVar pid meth
    -- set input arguments
    aftarg <- setArgs before meth args'
    -- trigger task
    afttag <- ctxInsTrans' aftarg $ envar I.=: I.true
    -- pause and wait for task to complete
    aftpause <- ctxInsTrans' afttag I.SPause
    aftwait  <- ctxInsTrans' aftpause $ I.SAssume $ envar I.=== I.false
    -- copy out arguments and retval
    aftout <- copyOutArgs aftwait meth args'
    case (mlhs, retIVar pid meth) of
         (Nothing, _)          -> ctxInsTrans aftout after I.SNop
         (Just lhs, Just rvar) -> do lhs' <- exprToIExpr lhs
                                     ctxInsTrans aftout after $ lhs' I.=: rvar


-- Common part of methInline and taskCall

-- assign input arguments to a method
setArgs :: I.Loc -> Method -> [I.Expr] -> State CFACtx I.Loc 
setArgs before meth args = do
    pid <- gets ctxPID
    foldM (\bef (farg,aarg) -> ctxInsTrans' bef $ (globaliseVar pid meth farg) I.=: aarg) 
          before $ filter (\(a,_) -> argDir a == ArgIn) $ zip (methArg meth) args

-- copy out arguments
copyOutArgs :: I.Loc -> Method -> [I.Expr] -> State CFACtx I.Loc
copyOutArgs loc meth args = do
    pid <- gets ctxPID
    foldM (\loc (farg,aarg) -> ctxInsTrans' loc $ aarg I.=: (globaliseVar pid meth farg)) loc $ 
          filter (\(a,_) -> argDir a == ArgOut) $ zip (methArg meth) args


-- Variables:
-- * Processes (top-level), methods, procedures, controllable tasks - single copy of local variables and input arguments
-- * Uncontrollable, invisible tasks - per-PID copies of local variables and input arguments

--spec2Internal :: Spec -> I.Spec
--spec2Internal s = I.Spec senum svar sproc sctl sinvis sinit sgoal
--    where ?spec = specSimplify s -- preprocessing
--          senum = mapMaybe (\d -> case tspec d of
--                                     EnumSpec _ es -> I.Enum (sname d) (map sname es)
--                                     _             -> Nothing) (specType ?spec)
--          sproc = concat $ map procTree (specProcess ?spec)
--          -- TODO: controllable processes
--
--
--                 { specEnum         :: [Enumeration]
--                 , specVar          :: [Var]
--                 , specProcess      :: [Process]
--                 , specInit         :: Process
--                 , specGoal         :: [Goal] 
--                 }


-- Recursively construct CFAs for the process and its children
procTree :: (?spec::Spec) => Process -> [I.Process]
procTree p = 
    let pid = [sname p]
        cfa = procToCFA pid p
        scope = ScopeProcess tmMain p
    in (I.Process (pidToName pid) cfa) : (procTreeRec pid scope (procStatement p) (procLMap pid p))
        
fprocTree :: (?spec::Spec) => PID -> Scope -> NameMap -> (Ident, Statement) -> [I.Process]
fprocTree parpid parscope lmap (n,stat) = 
    let pid = parpid ++ [sname n]
        cfa = fprocToCFA pid lmap parscope stat 
    in (I.Process (pidToName pid) cfa) : (procTreeRec pid parscope stat lmap)

taskProcTree :: (?spec::Spec) => PID -> Method -> [I.Process]
taskProcTree parpid meth = 
    let pid = parpid ++ [sname meth]
        cfa = taskToCFA parpid meth
    in (I.Process (pidToName pid) cfa) : (procTreeRec parpid (ScopeMethod tmMain meth) (fromRight $ methBody meth) (methodLMap parpid meth))

-- Recursive step of the algorithm: find all child subprocess of a statement
procTreeRec :: (?spec::Spec) => PID -> Scope -> Statement -> NameMap -> [I.Process]
procTreeRec pid scope stat lmap = tasks ++ forked
    where
    -- controllable/uncontrollable tasks invoked by the process
    tasks  = concatMap (taskProcTree pid)
             $ filter (((flip elem) [Task Controllable, Task Uncontrollable]) . methCat)
             $ procCallees scope stat
    -- spawned processes
    forked = concatMap (fprocTree pid scope lmap) $ forkedProcs stat
    



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
