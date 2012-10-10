{-# LANGUAGE ImplicitParams #-}

module StatementInline(statSimplify, 
                       statToCFA) where

import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe

import Util hiding (name)
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
import Var
import Method
import Process
import Type
import ExprInline

import qualified ISpec as I

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
                                      in ss ++ [SWait p c']
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
statToCFA :: (?spec::Spec, ?procs::[ProcTrans]) => I.Loc -> Statement -> State CFACtx I.Loc
statToCFA before (SSeq _ ss) = foldM statToCFA before ss
statToCFA before (SPause _)  = ctxPause before I.true
statToCFA before (SWait _ c) = do ci <- exprToIExprDet c
                                  ctxPause before ci
statToCFA before (SStop _)   = do after <- ctxInsLocLab I.LFinal
                                  ctxInsTrans before after I.nop
                                  return after
statToCFA before stat        = do after <- ctxInsLoc
                                  statToCFA' before after stat
                                  return after

-- Only safe to call from statToCFA.  Do not call this function directly!
statToCFA' :: (?spec::Spec, ?procs::[ProcTrans]) => I.Loc -> I.Loc -> Statement -> State CFACtx ()
statToCFA' before after (SVarDecl _ _) = ctxInsTrans before after I.nop
statToCFA' before after (SReturn _ rval) = do
    -- add transition before before to return location
    lhs <- gets ctxLHS
    ret <- gets ctxRetLoc
    stat <- case rval of 
                 Nothing -> return I.nop
                 Just v  -> case lhs of
                                 Nothing  -> return I.nop
                                 Just lhs -> do ScopeMethod _ m <- gets ctxScope
                                                vi <- exprToIExpr v (fromJust $ methRettyp m)
                                                return $ lhs I.=: vi
    ctxInsTrans before ret stat

statToCFA' before after (SPar _ ps) = do
    pid <- gets ctxPID
    -- child process pids
    let pids  = map (childPID pid . fst) ps
    -- enable child processes
    aften <- foldM (\bef pid -> ctxInsTrans' bef $ mkEnVar pid Nothing I.=: I.true) before pids
    let mkFinalCheck pid = I.disj $ map (\loc -> mkPCVar pid I.=== mkPC pid loc) $ pFinal p
                           where p = fromJustMsg ("mkFinalCheck: process " ++ pidToName pid ++ " unknown") $ 
                                     find ((== pid) . pPID) ?procs
    -- pause and wait for all of them to reach final states
    aftwait <- ctxPause aften $ I.conj $ map mkFinalCheck pids
    -- Disable forked processes and bring them back to initial states
    aftreset <- foldM (\bef pid -> ctxInsTrans' bef $ mkPCVar pid I.=: mkPC pid I.cfaInitLoc) aftwait pids
    aftdisable <- foldM (\bef pid -> ctxInsTrans' bef $ mkEnVar pid Nothing I.=: I.false) aftreset pids
    ctxInsTrans aftdisable after I.nop

statToCFA' before after (SForever _ stat) = do
    brkLoc <- gets ctxBrkLoc
    ctxPutBrkLoc after
    -- loc' = end of loop body
    loc' <- statToCFA before stat 
    -- loop-back transition
    ctxInsTrans loc' after I.nop
    ctxPutBrkLoc brkLoc

statToCFA' before after (SDo _ stat cond) = do
    brkLoc <- gets ctxBrkLoc
    cond' <- exprToIExpr cond (BoolSpec nopos)
    ctxInsTrans before after (I.SAssume $ I.EUnOp Not cond')
    -- after condition has been checked, before the body
    befbody <- ctxInsTrans' before (I.SAssume cond')
    -- body
    ctxPutBrkLoc after
    aftbody <- statToCFA befbody stat
    -- loop-back transition
    ctxInsTrans aftbody before I.nop
    ctxPutBrkLoc brkLoc

statToCFA' before after (SWhile _ cond stat) = do
    brkLoc <- gets ctxBrkLoc
    cond' <- exprToIExpr cond (BoolSpec nopos)
    ctxPutBrkLoc after
    aftbody <- statToCFA before stat
    ctxPutBrkLoc brkLoc
    -- loop-back transition
    ctxInsTrans aftbody before (I.SAssume cond')
    -- exit loop transition
    ctxInsTrans aftbody after (I.SAssume $ I.EUnOp Not cond')

statToCFA' before after (SFor _ (minit, cond, inc) body) = do
    brkLoc <- gets ctxBrkLoc
    cond' <- exprToIExpr cond (BoolSpec nopos)
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
    ctxInsTrans aftinc befbody I.nop

statToCFA' before after (SChoice _ ss) = do
    mapM (\s -> do aft <- statToCFA before s
                   ctxInsTrans aft after I.nop) ss
    return ()

statToCFA' before after (SBreak _) = do
    brkLoc <- gets ctxBrkLoc
    ctxInsTrans before brkLoc I.nop

statToCFA' before after (SInvoke _ mref as) = do
    scope <- gets ctxScope
    let meth = snd $ getMethod scope mref
    case methCat meth of
         Task Controllable   -> taskCall before after meth as Nothing
         Task Uncontrollable -> taskCall before after meth as Nothing
         _                   -> methInline before after meth as Nothing

statToCFA' before after (SAssert _ cond) = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.SAssume cond')
    ctxInsTrans before I.cfaErrLoc (I.SAssume $ I.EUnOp Not cond')

statToCFA' before after (SAssume _ cond) = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.SAssume cond')

statToCFA' before after (SAssign _ lhs (EApply _ mref args)) = do
    scope <- gets ctxScope
    let meth = snd $ getMethod scope mref
    case methCat meth of
         Task Controllable   -> taskCall before after meth args (Just lhs)
         Task Uncontrollable -> taskCall before after meth args (Just lhs)
         _                   -> methInline before after meth args (Just lhs)

statToCFA' before after (SAssign _ lhs rhs) = do
    scope <- gets ctxScope
    lhs' <- exprToIExprDet lhs
    rhs' <- let ?scope = scope in exprToIExpr rhs (tspec lhs)
    ctxInsTrans before after $ lhs' I.=: rhs'

statToCFA' before after (SITE _ cond sthen mselse) = do
    befthen <- statToCFA before (SAssume nopos cond)
    aftthen <- statToCFA befthen sthen
    ctxInsTrans aftthen after I.nop
    case mselse of
         Nothing -> return ()
         Just selse -> do befelse <- statToCFA before (SAssume nopos $ EUnOp nopos Not cond)
                          aftelse <- statToCFA befelse selse
                          ctxInsTrans aftelse after I.nop

statToCFA' before after (SCase _ e cs mdef) = do
    let negs = map (eAnd nopos . map (EBinOp nopos Neq e)) $ inits $ map fst cs
        cs' = map (\((c, st), neg) -> (EBinOp nopos And (EBinOp nopos Eq e c) neg, st)) $ zip cs negs
        cs'' = case mdef of
                    Nothing  -> cs'
                    Just def -> cs' ++ [(last negs, def)]
    mapM (\(c,st) -> do befst <- statToCFA before (SAssume nopos c)
                        aftst <- statToCFA befst  st
                        ctxInsTrans aftst after I.nop) cs''
    return ()


statToCFA' before after (SMagic _ obj) = do
    -- magic block flag
    aftmag <- ctxInsTrans' before $ mkMagicVar I.=: I.true
    -- wait for magic flag to be false
    aftwait <- ctxPause aftmag $ mkMagicVar I.=== I.false
    aftass <- case obj of
                   Left _     -> return aftwait
                   Right cond -> statToCFA aftwait $ SAssert nopos cond
    ctxInsTrans aftass after I.nop  

methInline :: (?spec::Spec,?procs::[ProcTrans]) => I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> State CFACtx ()
methInline before after meth args mlhs = do
    -- save current context
    befctx <- get
    let pid = ctxPID befctx
    lhs <- case mlhs of
                Nothing  -> return Nothing
                Just lhs -> (liftM Just) $ exprToIExprDet lhs
    -- set input arguments
    aftarg <- setArgs before meth args
    aftpause <- ctxPause aftarg $ I.true
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
    aftbody <- statToCFA aftpause (fromRight $ methBody meth)
    ctxInsTrans aftbody retloc I.nop

    -- copy out arguments
    aftout <- copyOutArgs retloc meth args
    aftpause <- ctxPause aftout $ I.true
    -- nop-transition to after
    ctxInsTrans aftpause after I.nop
    -- restore context
    ctxPutBrkLoc $ ctxBrkLoc befctx
    ctxPutRetLoc $ ctxRetLoc befctx
    ctxPutLNMap  $ ctxLNMap  befctx
    ctxPutLHS    $ ctxLHS    befctx


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
    afttag <- ctxInsTrans' aftarg $ envar I.=: I.true
    -- pause and wait for task to complete
    aftwait <- ctxPause afttag $ envar I.=== I.false
    -- copy out arguments and retval
    aftout <- copyOutArgs aftwait meth args
    case (mlhs, mkRetVar (Just pid) meth) of
         (Nothing, _)          -> ctxInsTrans aftout after I.nop
         (Just lhs, Just rvar) -> do lhs' <- exprToIExprDet lhs
                                     ctxInsTrans aftout after $ lhs' I.=: rvar


-- Common part of methInline and taskCall

-- assign input arguments to a method
setArgs :: (?spec::Spec) => I.Loc -> Method -> [Expr] -> State CFACtx I.Loc 
setArgs before meth args = do
    pid <- gets ctxPID
    foldM (\bef (farg,aarg) -> do aarg' <- exprToIExpr aarg (tspec farg)
                                  ctxInsTrans' bef $ (mkVar (Just pid) (Just meth) farg) I.=: aarg') 
          before $ filter (\(a,_) -> argDir a == ArgIn) $ zip (methArg meth) args

-- copy out arguments
copyOutArgs :: (?spec::Spec) => I.Loc -> Method -> [Expr] -> State CFACtx I.Loc
copyOutArgs loc meth args = do
    pid <- gets ctxPID
    foldM (\loc (farg,aarg) -> do aarg' <- exprToIExprDet aarg
                                  ctxInsTrans' loc $ aarg' I.=: (mkVar (Just pid) (Just meth) farg)) loc $ 
          filter (\(a,_) -> argDir a == ArgOut) $ zip (methArg meth) args
