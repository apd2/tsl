{-# LANGUAGE ImplicitParams #-}

module StatementInline(statSimplify, 
                       procStatToCFA) where

import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe
import Debug.Trace

import Util hiding (name,trace)
import Inline
import TSLUtil
import Spec
import Pos
import Name
import NS
import Statement
import Expr
import ExprOps
import Template
import TVar
import Method
import Process
import Type
import ExprInline

import qualified ISpec   as I
import qualified IExpr   as I
import qualified CFA     as I
import qualified IVar    as I
import qualified CFASpec as C

statSimplify :: (?spec::Spec, ?scope::Scope, ?uniq::Uniq) => Statement -> Statement
statSimplify s = sSeq (pos s) $ statSimplify' s

statSimplify' :: (?spec::Spec, ?scope::Scope, ?uniq::Uniq) => Statement -> [Statement]
statSimplify' (SVarDecl p v) = 
    case varInit v of
         Just e  -> (SVarDecl p v{varInit = Nothing}) :
                    (statSimplify' $ SAssign p (ETerm (pos $ varName v) [varName v]) e)
         Nothing -> (SVarDecl p v{varInit = Nothing}) :
                    (statSimplify' $ SAssign p (ETerm (pos $ varName v) [varName v]) (ENonDet nopos))

statSimplify' (SReturn p (Just e)) = 
    let (ss,e') = exprSimplify e
    in ss ++ [SReturn p (Just e')]

statSimplify' (SSeq p ss)           = [SSeq p $ concatMap statSimplify' ss]
statSimplify' (SPar p ss)           = [SPar p $ map (mapSnd statSimplify) ss]
statSimplify' (SForever p s)        = [SForever p $ statSimplify s]
statSimplify' (SDo p b c)           = let (ss,c') = exprSimplify c
                                      in [SDo p (sSeq (pos b) $ statSimplify' b ++ ss) c']
statSimplify' (SWhile p c b)        = let (ss,c') = exprSimplify c
                                      in ss ++ [SWhile p c' (sSeq (pos b) $ statSimplify' b ++ ss)]
statSimplify' (SFor p (mi, c, s) b) = let i' = case mi of
                                                    Nothing -> []
                                                    Just i  -> statSimplify' i
                                          (ss,c') = exprSimplify c
                                          s' = statSimplify s
                                      in i' ++ ss ++ [SFor p (Nothing, c',s') (sSeq (pos b) $ statSimplify' b ++ ss)]
statSimplify' (SChoice p ss)        = [SChoice p $ map statSimplify ss]
statSimplify' (SInvoke p mref as)   = -- Order of argument evaluation is undefined in C;
                                      -- Go left-to-right
                                      let (ss, as') = unzip $ map exprSimplify as
                                      in (concat ss) ++ [SInvoke p mref $ as']
statSimplify' (SWait p c)           = let (ss,c') = exprSimplify c
                                      in (SPause p) : (ss ++ [SAssume p c'])
statSimplify' (SAssert p c)         = let (ss,c') = exprSimplify c
                                      in ss ++ [SAssert p c']
statSimplify' (SAssume p c)         = let (ss,c') = exprSimplify c
                                      in ss ++ [SAssume p c']
statSimplify' (SAssign p l r)       = -- Evaluate lhs first
                                      let (ssl,l') = exprSimplify l
                                          ssr = exprSimplifyAsn p l' r
                                      in ssl ++ ssr
statSimplify' (SITE p c t me)       = let (ss,c') = exprSimplify c
                                      in ss ++ [SITE p c' (statSimplify t) (fmap statSimplify me)]
statSimplify' (SCase p c cs md)     = -- Case labels must be side-effect-free, so it is ok to 
                                      -- evaluate them in advance
                                      let (ssc,c')   = exprSimplify c
                                          (sscs,clabs') = unzip $ map exprSimplify (fst $ unzip cs)
                                          cstats = map statSimplify (snd $ unzip cs)
                                      in (concat sscs) ++ ssc ++ [SCase p c' (zip clabs' cstats) (fmap statSimplify md)]
statSimplify' (SMagic p (Right e))  = let (ss,e') = exprSimplify e
                                      in (SMagic p (Right $ EBool (pos e) True)):(ss ++ [SAssert (pos e) e'])
statSimplify' st                    = [st]



----------------------------------------------------------
-- Convert statement to CFA
----------------------------------------------------------
statToCFA :: (?spec::Spec, ?procs::[C.Process]) => I.Loc -> Statement -> State CFACtx I.Loc
statToCFA before   (SSeq _ ss)    = foldM statToCFA before ss
statToCFA before s@(SPause _)     = do ctxLocSetAct before (I.ActStat s)
                                       ctxPause before I.true
statToCFA before s@(SWait _ c)    = do ctxLocSetAct before (I.ActStat s)
                                       ci <- exprToIExprDet c
                                       ctxPause before ci
statToCFA before s@(SStop _)      = do ctxLocSetAct before (I.ActStat s)
                                       ctxFinal before
statToCFA before   (SVarDecl _ _) = return before
statToCFA before   s@stat         = do ctxLocSetAct before (I.ActStat s)
                                       after <- ctxInsLoc
                                       statToCFA' before after stat
                                       return after

-- Only safe to call from statToCFA.  Do not call this function directly!
statToCFA' :: (?spec::Spec, ?procs::[C.Process]) => I.Loc -> I.Loc -> Statement -> State CFACtx ()
statToCFA' before after (SReturn _ rval) = do
    -- add transition before before to return location
    lhs   <- gets ctxLHS
    ret   <- gets ctxRetLoc
    case rval of 
         Nothing -> ctxInsTrans before ret I.TranReturn
         Just v  -> case lhs of
                         Nothing  -> ctxInsTrans before ret I.TranReturn
                         Just lhs -> do scope@(ScopeMethod _ m) <- gets ctxScope
                                        let t = fromJust $ methRettyp m
                                        vi <- exprToIExprs v t
                                        let asns = map I.TranStat
                                                   $ zipWith I.SAssign (I.exprScalars lhs (mkType $ Type scope t))
                                                                       (concatMap (uncurry I.exprScalars) vi)
                                        aftargs <- ctxInsTransMany' before asns
                                        ctxInsTrans aftargs ret I.TranReturn

statToCFA' before after (SPar _ ps) = do
    pid <- gets ctxPID
    -- child process pids
    let pids  = map (childPID pid . fst) ps
    -- enable child processes
    aften <- ctxInsTransMany' before $ map (\pid -> I.TranStat $ mkEnVar pid Nothing I.=: I.true) pids
    let mkFinalCheck (n,_) = I.disj $ map (\loc -> mkPCVar pid I.=== mkPC pid loc) $ I.cfaFinal $ C.procCFA p
                             where pid = childPID pid n
                                   p = fromJustMsg ("mkFinalCheck: process " ++ pidToName pid ++ " unknown") 
                                       $ find ((== sname n) . C.procName) ?procs
    -- pause and wait for all of them to reach final states
    aftwait <- ctxPause aften $ I.conj $ map mkFinalCheck ps
    -- Disable forked processes and bring them back to initial states
    aftreset <- ctxInsTransMany' aftwait $ map (\pid -> I.TranStat $ mkPCVar pid I.=: mkPC pid I.cfaInitLoc) pids
    aftdisable <- ctxInsTransMany' aftreset $ map  (\pid -> I.TranStat $ mkEnVar pid Nothing I.=: I.false) pids
    ctxInsTrans aftdisable after I.TranNop

statToCFA' before after (SForever _ stat) = do
    ctxPushBrkLoc after
    -- create target for loopback transition
    loopback <- ctxInsTrans' before I.TranNop
    -- loc' = end of loop body
    loc' <- statToCFA loopback stat
    -- loop-back transition
    ctxInsTrans loc' loopback I.TranNop
    ctxPopBrkLoc

statToCFA' before after (SDo _ stat cond) = do
    cond' <- exprToIExpr cond (BoolSpec nopos)
    ctxPushBrkLoc after
    -- create target for loopback transition
    loopback <- ctxInsTrans' before I.TranNop
    aftbody <- statToCFA loopback stat
    ctxLocSetAct aftbody (I.ActExpr cond)
    ctxPopBrkLoc
    -- loop-back transition
    ctxInsTrans aftbody loopback (I.TranStat $ I.SAssume cond')
    -- exit loop transition
    ctxInsTrans aftbody after (I.TranStat $ I.SAssume $ I.EUnOp Not cond')

statToCFA' before after (SWhile _ cond stat) = do
    cond' <- exprToIExpr cond (BoolSpec nopos)
    -- create target for loopback transition
    loopback <- ctxInsTrans' before I.TranNop
    ctxLocSetAct loopback (I.ActExpr cond)
    ctxInsTrans loopback after (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
    -- after condition has been checked, before the body
    befbody <- ctxInsTrans' loopback (I.TranStat $ I.SAssume cond')
    -- body
    ctxPushBrkLoc after
    aftbody <- statToCFA befbody stat
    -- loop-back transition
    ctxInsTrans aftbody loopback I.TranNop
    ctxPopBrkLoc

statToCFA' before after (SFor _ (minit, cond, inc) body) = do
    cond' <- exprToIExpr cond (BoolSpec nopos)
    aftinit <- case minit of
                    Nothing   -> return before
                    Just init -> statToCFA before init
    -- create target for loopback transition
    loopback <- ctxInsTrans' aftinit I.TranNop
    ctxLocSetAct loopback (I.ActExpr cond)
    ctxInsTrans loopback after (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
    -- before loop body
    befbody <- ctxInsTrans' loopback $ I.TranStat $ I.SAssume cond'
    ctxPushBrkLoc after
    aftbody <- statToCFA befbody body
    -- after increment is performed at the end of loop iteration
    aftinc <- statToCFA aftbody inc
    ctxPopBrkLoc
    -- loopback transition
    ctxInsTrans aftinc loopback I.TranNop

statToCFA' before after (SChoice _ ss) = do
    v <- ctxInsTmpVar $ mkChoiceType $ length ss
    mapIdxM (\s i -> do aftAssume <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EVar (I.varName v) I.=== mkChoice v i)
                        aft <- statToCFA aftAssume s
                        ctxInsTrans aft after I.TranNop) ss
    return ()

statToCFA' before after (SBreak _) = do
    brkLoc <- gets ctxBrkLoc
    ctxInsTrans before brkLoc I.TranNop

statToCFA' before after (SInvoke _ mref as) = do
    scope <- gets ctxScope
    let meth = snd $ getMethod scope mref
    case methCat meth of
         Task Controllable   -> taskCall before after meth as Nothing
         Task Uncontrollable -> taskCall before after meth as Nothing
         _                   -> methInline before after meth as Nothing

statToCFA' before after (SAssert _ cond) = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.TranStat $ I.SAssume cond')
    ctxErrTrans before (I.TranStat $ I.SAssume $ I.EUnOp Not cond')

statToCFA' before after (SAssume _ cond) = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.TranStat $ I.SAssume cond')

statToCFA' before after (SAssign _ lhs (EApply _ mref args)) = do
    scope <- gets ctxScope
    let meth = snd $ getMethod scope mref
    case methCat meth of
         Task Controllable   -> taskCall before after meth args (Just lhs)
         Task Uncontrollable -> taskCall before after meth args (Just lhs)
         _                   -> methInline before after meth args (Just lhs)

statToCFA' before after st@(SAssign _ lhs rhs) = do
    scope <- gets ctxScope
    let ?scope = scope
    let t = mkType $ typ lhs
    lhs' <- exprToIExprDet lhs
    rhs' <- exprToIExprs rhs (tspec lhs)
    ctxInsTransMany before after $ map I.TranStat
                                 $ zipWith I.SAssign (I.exprScalars lhs' t) 
                                                     (concatMap (uncurry I.exprScalars) rhs')

statToCFA' before after (SITE _ cond sthen mselse) = do
    cond' <- exprToIExprDet cond
    befthen <- ctxInsTrans' before (I.TranStat $ I.SAssume cond')
    aftthen <- statToCFA befthen sthen
    ctxInsTrans aftthen after I.TranNop
    befelse <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
    aftelse <- case mselse of
                    Nothing    -> return befelse
                    Just selse -> statToCFA befelse selse
    ctxInsTrans aftelse after I.TranNop

statToCFA' before after (SCase _ e cs mdef) = do
    let negs = map (eAnd nopos . map (EBinOp nopos Neq e)) $ inits $ map fst cs
        cs' = map (\((c, st), neg) -> (EBinOp nopos And (EBinOp nopos Eq e c) neg, Just st)) $ zip cs negs
        cs'' = case mdef of
                    Nothing  -> cs' ++ [(last negs, Nothing)]
                    Just def -> cs' ++ [(last negs, Just def)]
    mapM (\(c,st) -> do c' <- exprToIExprDet c
                        befst <- ctxInsTrans' before (I.TranStat $ I.SAssume c')
                        aftst <- case st of 
                                      Nothing -> return befst
                                      Just st -> statToCFA befst st
                        ctxInsTrans aftst after I.TranNop) cs''
    return ()


statToCFA' before after (SMagic _ obj) = do
    -- magic block flag
    aftcheck <- ctxInsTrans' before $ I.TranStat $ I.SAssume $ mkMagicVar I.=== I.false
    aftmag <- ctxInsTrans' aftcheck $ I.TranStat $ mkMagicVar I.=: I.true
    -- wait for magic flag to be false
    aftwait <- ctxPause aftmag $ mkMagicVar I.=== I.false
    ctxInsTrans aftwait after I.TranNop

methInline :: (?spec::Spec,?procs::[C.Process]) => I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> State CFACtx ()
methInline before after meth args mlhs = do
    -- save current context
    pid <- gets ctxPID
    let scope = ScopeMethod tmMain meth
    lhs <- case mlhs of
                Nothing  -> return Nothing
                Just lhs -> (liftM Just) $ exprToIExprDet lhs
    -- set input arguments
    aftarg <- setArgs before meth args
--    aftpause1 <- case methCat meth of
--                      Task _ -> ctxPause aftarg I.true
--                      _      -> return aftarg
    -- set return location
    retloc <- ctxInsLoc
    -- clear break location
    ctxPushBrkLoc $ error "break outside a loop"
    -- change syntactic scope
    ctxPushScope scope retloc lhs (methodLMap pid meth)
    -- build CFA of the method
    aftcall <- ctxInsTrans' aftarg (I.TranCall scope)
    aftbody <- statToCFA aftcall (fromRight $ methBody meth)
    ctxInsTrans aftbody retloc I.TranReturn
    -- restore syntactic scope
    ctxPopScope
    -- copy out arguments
    aftout <- copyOutArgs retloc meth args
--    aftpause2 <- case methCat meth of
--                      Task _ -> ctxPause aftout I.true
--                      _      -> return aftout
    -- nop-transition to after
    ctxInsTrans aftout after I.TranNop
    -- restore context
    ctxPopBrkLoc


taskCall :: (?spec::Spec) => I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> State CFACtx ()
taskCall before after meth args mlhs = do
    pid <- gets ctxPID
    lhs <- case mlhs of
                Nothing  -> return Nothing
                Just lhs -> (liftM Just) $ exprToIExprDet lhs
    let envar = mkEnVar pid (Just meth)
    -- set input arguments
    aftarg <- setArgs before meth args
    -- trigger task
    afttag <- ctxInsTrans' aftarg $ I.TranStat $ envar I.=: I.true
    -- pause and wait for task to complete
    aftwait <- ctxPause afttag $ mkWaitForTask pid meth
    -- copy out arguments and retval
    aftout <- copyOutArgs aftwait meth args
    case (mlhs, mkRetVar (Just pid) meth) of
         (Nothing, _)          -> ctxInsTrans aftout after I.TranNop
         (Just lhs, Just rvar) -> do let t = mkType $ Type (ScopeTemplate tmMain) (fromJust $ methRettyp meth)
                                     lhs' <- exprToIExprDet lhs
                                     ctxInsTransMany aftout after $ map I.TranStat
                                                                  $ zipWith I.SAssign (I.exprScalars lhs' t) 
                                                                                      (I.exprScalars rvar t)


-- Common part of methInline and taskCall

-- assign input arguments to a method
setArgs :: (?spec::Spec) => I.Loc -> Method -> [Expr] -> State CFACtx I.Loc 
setArgs before meth args = do
    pid   <- gets ctxPID
    foldM (\bef (farg,aarg) -> do aarg' <- exprToIExprs aarg (tspec farg)
                                  let t = mkType $ Type (ScopeTemplate tmMain) (tspec farg)
                                  ctxInsTransMany' bef $ map I.TranStat
                                                       $ zipWith I.SAssign (I.exprScalars (mkVar (Just pid) (Just meth) farg) t) 
                                                                           (concatMap (uncurry I.exprScalars) aarg'))
          before $ filter (\(a,_) -> argDir a == ArgIn) $ zip (methArg meth) args

-- copy out arguments
copyOutArgs :: (?spec::Spec) => I.Loc -> Method -> [Expr] -> State CFACtx I.Loc
copyOutArgs loc meth args = do
    pid <- gets ctxPID
    foldM (\loc (farg,aarg) -> do aarg' <- exprToIExprDet aarg
                                  let t = mkType $ Type (ScopeTemplate tmMain) (tspec farg)
                                  ctxInsTransMany' loc $ map I.TranStat
                                                       $ zipWith I.SAssign (I.exprScalars aarg' t) 
                                                                           (I.exprScalars (mkVar (Just pid) (Just meth) farg) t)) loc $ 
          filter (\(a,_) -> argDir a == ArgOut) $ zip (methArg meth) args

----------------------------------------------------------
-- Top-level function: convert process statement to CFA
----------------------------------------------------------

procStatToCFA :: (?spec::Spec, ?procs::[C.Process]) => Statement -> I.Loc -> State CFACtx I.Loc
procStatToCFA stat before = do
    after <- statToCFA before stat
    modify (\ctx -> ctx {ctxCFA = I.cfaAddNullPtrTrans (ctxCFA ctx) mkNullVar})
    return after
