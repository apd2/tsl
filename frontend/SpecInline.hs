{-# LANGUAGE ImplicitParams #-}

-- Convert flattened spec to internal representation
module SpecInline () where

import Data.List
import Data.Maybe
import qualified Data.Map as M
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
    in let ?scope = ScopeMethod (head $ specTemplate ?spec) m 
       in nub $ (name m):(statMethods $ fromRight $ methBody m)

-- Child processes spawned by the statement (including processes spawned 
-- by tasks invoked by the statement)
procChildren :: (?spec::Spec, ?scope::Scope) => Statement -> [(Ident, Scope, Statement)]
procChildren st = map (\(n, st) -> (n,?scope,st)) (statSubprocessNonrec st) ++
                  concatMap (\(tm',m) -> map (\(n,st) -> (n, ScopeMethod tm' m, st)) $ statSubprocessNonrec $ fromRight $ methBody m) ms
    where tm = head $ specTemplate ?spec
          ms = map (getMethod (ScopeTemplate tm) . (\n -> MethodRef (pos n) [n])) $ statMethods st


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

-- Variable that stores return value of a task
retIVarName :: PID -> Method -> Maybe String
retIVarName pid meth = case methRettyp meth of
                            Nothing -> Nothing
                            Just _  -> Just $ globaliseName pid (Ident nopos (sname meth ++ "$ret"))

-- Variable used to make a forked process runnable
--runIVarName :: PID -> String
--runIVarName pid = globaliseName pid (Ident nopos "$run")


----------------------------------------------------------------------
-- Convert expressions to internal format
----------------------------------------------------------------------

exprToIExpr :: Expr -> State CFACtx I.Expr
exprToIExpr = error $ "Not implemented: exprToIExpr"

----------------------------------------------------------------------
-- CFA transformation
----------------------------------------------------------------------


type NameMap = M.Map Ident I.Expr

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
ctxInsTrans from to stat = do
    ctx <- get
    let cfa' = I.cfaInsTrans from to stat $ ctxCFA ctx
    put $ ctx {ctxCFA = cfa'}

ctxPutBrkLoc :: I.Loc -> State CFACtx ()
ctxPutBrkLoc loc = do
    ctx <- get
    put $ ctx {ctxBrkLoc = loc}


-- Convert process or forked process to CFA
-- For a forked process the mparpid argument is the PID of the process in 
-- whose syntactic scope the present process is located.
procToCFA :: (?spec::Spec) => PID -> NameMap -> Process -> Statement -> I.CFA
procToCFA pid gmap proc stat = ctxCFA ctx'
    where -- Add process-local variables to nmap
          lmap  = M.fromList $ map (\v -> (name v, I.EVar $ globaliseName pid v)) (procVar proc)
          ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = ScopeProcess (head $ specTemplate ?spec) proc
                       , ctxCFA    = I.newCFA
                       , ctxRetLoc = error "return from a process"
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = Nothing
                       , ctxGNMap  = gmap
                       , ctxLNMap  = lmap}
          ctx' = execState (statToCFA I.cfaInitLoc stat) ctx


fprocToCFA :: (?spec::Spec) => PID -> NameMap -> Process -> Statement -> PID -> I.CFA
fprocToCFA pid gmap proc stat parpid = ctxCFA ctx'
    where -- Add process-local variables to nmap
          lmap  = M.fromList $ map (\v -> (name v, I.EVar $ globaliseName parpid v)) (procVar proc)
          ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = ScopeProcess (head $ specTemplate ?spec) proc
                       , ctxCFA    = I.newCFA
                       , ctxRetLoc = error "return from a process"
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = Nothing
                       , ctxGNMap  = gmap
                       , ctxLNMap  = lmap}
          ctx' = execState (statToCFA I.cfaInitLoc stat) ctx



taskToCFA :: (?spec::Spec) => PID -> NameMap -> Method -> I.CFA
taskToCFA pid gmap meth = ctxCFA ctx'
    where tm = (head $ specTemplate ?spec)
          stat = fromRight $ methBody meth
          lmap   = M.fromList $ 
                   map (\v -> (name v, I.EVar $ globaliseName pid v)) (methVar meth) ++
                   map (\a -> (name a, I.EVar $ globaliseName pid a)) (methArg meth)
          ctx = CFACtx { ctxPID    = pid 
                       , ctxScope  = ScopeMethod tm meth
                       , ctxCFA    = I.newCFA
                       , ctxRetLoc = I.cfaInitLoc
                       , ctxBrkLoc = error "break outside a loop"
                       , ctxLHS    = fmap I.EVar $ retIVarName pid meth
                       , ctxGNMap  = gmap
                       , ctxLNMap  = lmap}
          ctx' = execState (statToCFA I.cfaInitLoc stat) ctx


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
                                                return $ I.SAssign lhs vi
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
    befbody <- ctxInsLoc
    ctxInsTrans before befbody (I.SAssume cond')
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
    befbody <- ctxInsLoc
    ctxInsTrans aftinit befbody (I.SAssume cond')
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
    ctxInsTrans before after (I.SAssign lhs' rhs')

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


--               | SMagic   {stpos::Pos, magiccond::(Either Ident Expr)}


methInline :: I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> State CFACtx ()
methInline before after meth args mlhs = error $ "Not imlemented: methInline"

taskCall :: I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> State CFACtx ()
taskCall before after meth args mlhs = error $ "Not implemented: methInline"








-- Variables:
-- * Processes (top-level), methods, procedures, controllable tasks - single copy of local variables and input arguments
-- * Uncontrollable, invisible tasks - per-PID copies of local variables and input arguments

--spec2Internal :: Spec -> I.Spec
--spec2Internal s = I.Spec senum svar sproc sctl sinvis sinit sgoal
--    where ?spec = specSimplify s -- preprocessing
--          tmmain = head $ specTemplate ?spec
--          senum = mapMaybe (\d -> case tspec d of
--                                     EnumSpec _ es -> I.Enum (sname d) (map sname es)
--                                     _             -> Nothing) (specType ?spec)
--          tagvar            =
--          lvars             = 
--          initstat          = statSimplify $ -- compute init statement from global variable assignments and init blocks
--          (sinit, initvars) = proc2CFA initid (ScopeTemplate tmmain) initstat
--
--
--
---- Inline process and convert it to CFA form
--proc2CFA :: (?spec::Spec) => PID -> Scope -> Statement -> (I.CFA, [I.Var])
--proc2CFA pid scope st = (stat2CFA st', vars)
--    where st'  = procInline pid scope st
--          vars = map (\v -> I.Var ((sname v) VarState (tspec2Internal $ tspec v)) (statVar st')
--
--
---- Inline all method invocations in a process.  
---- The process must be in the preprocessed format
---- s   - syntactic scope of the statement (template, process, or method)
--procInline :: (?spec::Spec) => PID -> Scope -> Statement -> Process
--procInline pid scope st = 
--    let ?pid = pid
--        ?scope = scope
--        ?mlhs = Nothing
--        ?retlab = error "no retlab in a process"
--        vars = map (SVarDecl nopos) $ statRenameVars s st
--        st' = statInline pid scope st
--    in sseq (pos st) (vars++st')
--
----
----
----
--statInline :: (?spec::Spec,?pid::PID,?scope::Scope,?mlhs::Maybe Expr,?retlab::SrcLabel) -> Statement -> [Statement]
--statInline (SVarDecl _ _)       = []
--statInline (SReturn p Nothing)  = [SGoTo p ?retlab]
--statInline (SReturn p (Just e)) = case mlhs of
--                                       Nothing  -> [exprInline e, SGoTo p ?retlab]
--                                       Just lhs -> [SAssign p lhs (exprInline e), SGoTo p ?retlab]
--statInline (SSeq p ss)          = [SSeq p (concaMap statInline ss)]
--statInline (SPar p ss)          = [SPar p ss]
--statInline (SForever p s)       = [SForever p (sstatInline s)]
--statInline (SDo p b c)          = [SDo p (sstatInline b) (exprInline c)]
--statInline (SWhile p c b)       = [SWhile p (exprInline c) (sstatInline b)]
--statInline (SFor p (mi,c,s) b}  = [SFor p (fmap sstatInline mi, exprInline c, sstatInline s) (sstatInline b)]
--statInline (SChoice p ss)       = [SChoice p (map sstatInline ss)]
--statInline (SInvoke p mref as)  = callInline p mref as Nothing
--statInline (SAssert p c)        = [SAssert p (exprInline c)]
--statInline (SAssume p c)        = [SAssume p (exprInline c)]
--
---- TODO : assignment to output argument
--statInline (SAssign p l (EApply p' mref as)) = callInline p' mref as (Just $ exprInline l)
--statInline (SAssign p l r)      = [SAssign p (exprInline l) (exprInline r)]
--statInline (SITE p c t me)      = [SITE p (exprInline c) (statInline t) (fmap statInline me)]
--statInline (SCase p c cs md)    = [SCase p (exprInline c) (map (\(c,s) -> (exprInline c, statInline s)) cs) (fmap statInline md)]
--statInline (SMagic p (Right e)  = [SMagic p (Right $ exprInline e)]
--statInline st                   = st
--
--sstatInline = sseq . statInline
--
--callInline :: (?spec::Spec,?pid::PID,?scope::Scope) -> Pos -> MethodRef -> [Expr] -> Maybe LExpr -> [Statement]
--callInline p mref args mlhs = sseq $ pause ++ tag ++ sargs ++ body ++ [SSrcLab p ?retlab]
--    where (tm, m) = getMethod ?scope mref
--          pause = case methCat m of
--                       Task Controllable   -> [SPause p]
--                       Task Uncontrollable -> [SPause p]
--                       _                   -> []
--          tag = if methCat m `elem` [Task Controllable,Tasl Uncontrollable]
--                   then [SAssign (pos mref) tagExpr (taskTag m)]
--                   else []
--          argnames = map (argName m) (methArg m)
--          sargs = map (\n a -> SAssign (pos a) (ETerm (pos a) n) (exprInline a)) (zip argnames args)
--          (body,lab) = let ?scope  = ScopeMethod tm m
--                           ?mlhs   = mlhs
--                           ?retlab = labelFromPos p
--                       in (statInline $ fromRight $ methBody m, ?retlab)
