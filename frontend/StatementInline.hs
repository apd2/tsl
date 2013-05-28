{-# LANGUAGE ImplicitParams, TupleSections #-}

module StatementInline(statSimplify, 
                       procStatToCFA) where

import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Traversable as Tr

import Util hiding (name,trace)
import Inline
import TSLUtil
import Spec
import Pos
import Name
import NS
import Statement
import Expr
import TVar
import Method
import Type
import ExprInline

import qualified IExpr as I
import qualified CFA   as I
import qualified IVar  as I
import qualified ISpec as I

statSimplify :: (?spec::Spec, ?scope::Scope) => Statement -> NameGen Statement
statSimplify s = (liftM $ sSeq (pos s)) $ statSimplify' s

statSimplify' :: (?spec::Spec, ?scope::Scope) => Statement -> NameGen [Statement]
statSimplify' (SVarDecl p v) = 
    case varInit v of
         Just e  -> do asn <- (statSimplify' $ SAssign p (ETerm (pos $ varName v) [varName v]) e)
                       return $ SVarDecl p v{varInit = Nothing} : asn
         Nothing -> do asn <- statSimplify' $ SAssign p (ETerm (pos $ varName v) [varName v]) (ENonDet nopos)
                       return $ SVarDecl p v{varInit = Nothing} : asn

statSimplify' (SReturn p (Just e)) = do
    (ss,e') <- exprSimplify e
    return $ ss ++ [SReturn p (Just e')]

statSimplify' (SSeq p ss)           = (liftM $ return . SSeq p . concat) $ mapM statSimplify' ss
statSimplify' (SPar p ss)           = (liftM $ return . SPar p)          $ mapM (\(n,s) -> liftM (n,) $ statSimplify s) ss
statSimplify' (SForever p s)        = (liftM $ return . SForever p)      $ statSimplify s
statSimplify' (SDo p b c)           = do (ss,c') <- exprSimplify c
                                         b'      <- statSimplify' b
                                         return [SDo p (sSeq (pos b) (b'++ss)) c']
statSimplify' (SWhile p c b)        = do (ss,c') <- exprSimplify c
                                         b'      <- statSimplify' b
                                         return $ ss ++ [SWhile p c' (sSeq (pos b) (b'++ss))]
statSimplify' (SFor p (mi, c, s) b) = do i' <- case mi of
                                                    Nothing -> return []
                                                    Just i  -> statSimplify' i
                                         (ss,c') <- exprSimplify c
                                         s' <- statSimplify s
                                         b' <- statSimplify' b
                                         return $ i' ++ ss ++ [SFor p (Nothing, c',s') (sSeq (pos b) (b'++ss))]
statSimplify' (SChoice p ss)        = liftM (return . SChoice p)         $ mapM statSimplify ss
statSimplify' (SInvoke p mref as)   = -- Order of argument evaluation is undefined in C;
                                      -- Go left-to-right
                                      do (ss, as') <- liftM unzip $ mapM exprSimplify as
                                         return $ (concat ss) ++ [SInvoke p mref as']
statSimplify' (SWait p c)           = do (ss,c') <- exprSimplify c
                                         return $ case ss of
                                                       [] -> [SWait p c']
                                                       _  -> (SPause p) : (ss ++ [SAssume p c'])
statSimplify' (SAssert p c)         = do (ss,c') <- exprSimplify c
                                         return $ ss ++ [SAssert p c']
statSimplify' (SAssume p c)         = do (ss,c') <- exprSimplify c
                                         return $ ss ++ [SAssume p c']
statSimplify' (SAssign p l r)       = -- Evaluate lhs first
                                      do (ssl,l') <- exprSimplify l
                                         ssr <- exprSimplifyAsn p l' r
                                         return $ ssl ++ ssr
statSimplify' (SITE p c t me)       = do (ss,c') <- exprSimplify c
                                         t'      <- statSimplify t
                                         me'     <- Tr.sequence $ fmap statSimplify me
                                         return $ ss ++ [SITE p c' t' me']
statSimplify' (SCase p c cs md)     = -- Case labels must be side-effect-free, so it is ok to 
                                      -- evaluate them in advance
                                      do (ssc,c')      <- exprSimplify c
                                         (sscs,clabs') <- (liftM unzip) $ mapM exprSimplify (fst $ unzip cs)
                                         cstats        <- mapM statSimplify (snd $ unzip cs)
                                         md'           <- Tr.sequence $ fmap statSimplify md
                                         return $ concat sscs ++ ssc ++ [SCase p c' (zip clabs' cstats) md']
statSimplify' (SMagic p p2 (Right e)) = do (ss,e') <- exprSimplify e
                                           return $ (SMagic p p2 (Right $ EBool (pos e) True)):(ss ++ [SAssert (pos e) e'])
statSimplify' st                      = return [st]



----------------------------------------------------------
-- Convert statement to CFA
----------------------------------------------------------
statToCFA :: (?cont::Bool, ?spec::Spec, ?procs::[I.Process]) => I.Loc -> Statement -> State CFACtx I.Loc
statToCFA before   (SSeq _ ss)    = foldM statToCFA before ss
statToCFA before s@(SPause _)     = do ctxLocSetAct before (I.ActStat s)
                                       ctxPause before I.true (I.ActStat s)
statToCFA before s@(SWait _ c)    = do ctxLocSetAct before (I.ActStat s)
                                       ci <- exprToIExprDet c
                                       ctxPause before ci (I.ActStat s)
statToCFA before s@(SStop _)      = do ctxLocSetAct before (I.ActStat s)
                                       ctxFinal before
statToCFA before   (SVarDecl _ _) = return before
statToCFA before s@stat           = do ctxLocSetAct before (I.ActStat s)
                                       after <- ctxInsLoc
                                       statToCFA' before after stat
                                       return after

-- Only safe to call from statToCFA.  Do not call this function directly!
statToCFA' :: (?cont::Bool, ?spec::Spec, ?procs::[I.Process]) => I.Loc -> I.Loc -> Statement -> State CFACtx ()
statToCFA' before _ (SReturn _ rval) = do
    -- add transition before before to return location
    mlhs  <- gets ctxLHS
    ret   <- gets ctxRetLoc
    case rval of 
         Nothing -> ctxInsTrans before ret I.TranNop
         Just v  -> case mlhs of
                         Nothing  -> ctxInsTrans before ret I.TranNop
                         Just lhs -> do sc@(ScopeMethod _ m) <- gets ctxScope
                                        let t = fromJust $ methRettyp m
                                        vi <- exprToIExprs v t
                                        let asns = map I.TranStat
                                                   $ zipWith I.SAssign (I.exprScalars lhs (mkType $ Type sc t))
                                                                       (concatMap (uncurry I.exprScalars) vi)
                                        aftargs <- ctxInsTransMany' before asns
                                        ctxInsTrans aftargs ret I.TranNop

statToCFA' before after s@(SPar _ ps) = do
    pid <- gets ctxPID
    -- child process pids
    let pids  = map (childPID pid . fst) ps
    -- enable child processes
    aften <- ctxInsTransMany' before $ map (\pid' -> I.TranStat $ mkEnVar pid' Nothing I.=: I.true) pids
    let mkFinalCheck (n,_) = I.disj $ map (\loc -> mkPCVar pid' I.=== mkPC pid' loc) $ I.cfaFinal $ I.procCFA p
                             where pid' = childPID pid n
                                   p = fromJustMsg ("mkFinalCheck: process " ++ pidToName pid' ++ " unknown") 
                                       $ find ((== sname n) . I.procName) ?procs
    -- pause and wait for all of them to reach final states
    aftwait <- ctxPause aften (I.conj $ map mkFinalCheck ps) (I.ActStat s)
    -- Disable forked processes and bring them back to initial states
    aftreset <- ctxInsTransMany' aftwait $ map (\pid' -> I.TranStat $ mkPCVar pid' I.=: mkPC pid' I.cfaInitLoc) pids
    aftdisable <- ctxInsTransMany' aftreset $ map  (\pid' -> I.TranStat $ mkEnVar pid' Nothing I.=: I.false) pids
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
                    Nothing -> return before
                    Just st -> statToCFA before st
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
    _ <- mapIdxM (\s i -> do aftAssume <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EVar (I.varName v) I.=== mkChoice v i)
                             aft <- statToCFA aftAssume s
                             ctxInsTrans aft after I.TranNop) ss
    return ()

statToCFA' before _ (SBreak _) = do
    brkLoc <- gets ctxBrkLoc
    ctxInsTrans before brkLoc I.TranNop

statToCFA' before after s@(SInvoke _ mref as) = do
    sc <- gets ctxScope
    let meth = snd $ getMethod sc mref
    case methCat meth of
         Task Controllable   -> taskCall before after meth as Nothing s
         Task Uncontrollable -> taskCall before after meth as Nothing s
         _                   -> methInline before after meth as Nothing

statToCFA' before after (SAssert _ cond) = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.TranStat $ I.SAssume cond')
    ctxErrTrans before (I.TranStat $ I.SAssume $ I.EUnOp Not cond')

statToCFA' before after (SAssume _ cond) = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.TranStat $ I.SAssume cond')

statToCFA' before after s@(SAssign _ lhs (EApply _ mref args)) = do
    sc <- gets ctxScope
    let meth = snd $ getMethod sc mref
    case methCat meth of
         Task Controllable   -> taskCall before after meth args (Just lhs) s
         Task Uncontrollable -> taskCall before after meth args (Just lhs) s
         _                   -> methInline before after meth args (Just lhs)

statToCFA' before after (SAssign _ lhs rhs) = do
    sc <- gets ctxScope
    let ?scope = sc
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
    _ <- mapM (\(c,mst) -> do c' <- exprToIExprDet c
                              befst <- ctxInsTrans' before (I.TranStat $ I.SAssume c')
                              aftst <- case mst of 
                                            Nothing -> return befst
                                            Just st -> statToCFA befst st
                              ctxInsTrans aftst after I.TranNop) cs''
    return ()


statToCFA' before after s@(SMagic _ _ constr) = do
    -- magic block flag
    aftcheck <- ctxInsTrans' before $ I.TranStat $ I.SAssume $ mkMagicVar I.=== I.false
    aftmag <- ctxInsTrans' aftcheck $ I.TranStat $ mkMagicVar I.=: I.true
    -- wait for magic flag to be false
    let p = case constr of
                 Left  i -> pos i
                 Right c -> pos c
    aftwait <- ctxPause aftmag mkMagicDoneCond (I.ActStat $ atPos s p)
    ctxInsTrans aftwait after I.TranNop

methInline :: (?cont::Bool, ?spec::Spec,?procs::[I.Process]) => I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> State CFACtx ()
methInline before after meth args mlhs = do
    -- save current context
    pid <- gets ctxPID
    let sc = ScopeMethod tmMain meth
    lhs <- case mlhs of
                Nothing  -> return Nothing
                Just lhs -> (liftM Just) $ exprToIExprDet lhs
    -- set input arguments
    aftarg <- setArgs before meth args
    -- set return location
    retloc <- ctxInsLoc
    aftret <- ctxInsTrans' retloc I.TranReturn
    -- clear break location
    ctxPushBrkLoc $ error "break outside a loop"
    -- change syntactic scope
    ctxPushScope sc aftret lhs (methodLMap pid meth)
    -- build CFA of the method
    aftcall <- ctxInsTrans' aftarg (I.TranCall meth (Just aftret))
    aftbody <- statToCFA aftcall (fromRight $ methBody meth)
    ctxInsTrans aftbody retloc I.TranNop
    -- restore syntactic scope
    ctxPopScope
    -- copy out arguments
    aftout <- copyOutArgs aftret meth args
    -- nop-transition to after
    ctxInsTrans aftout after I.TranNop
    -- restore context
    ctxPopBrkLoc


taskCall :: (?cont::Bool, ?spec::Spec) => I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> Statement -> State CFACtx ()
taskCall before after meth args mlhs st | ?cont     = contTaskCall  before after meth args
                                        | otherwise = ucontTaskCall before after meth args mlhs st

contTaskCall :: (?spec::Spec) => I.Loc -> I.Loc -> Method -> [Expr] -> State CFACtx ()
contTaskCall before after meth args = do
    -- set tag
    afttag <- ctxInsTrans' before $ I.TranStat $ mkTagVar I.=: tagMethod meth
    -- set input arguments
    aftarg <- setArgs afttag meth args
    -- switch to uncontrollable state
    aftcont <- ctxInsTrans' aftarg $ I.TranStat $ mkContVar I.=: I.false
    -- $pid = $pidcont
    ctxInsTrans aftcont after $ I.TranStat $ mkPIDVar I.=: mkPIDEnum pidCont

ucontTaskCall :: (?spec::Spec) => I.Loc -> I.Loc -> Method -> [Expr] -> Maybe Expr -> Statement -> State CFACtx ()
ucontTaskCall before after meth args mlhs st = do
    pid <- gets ctxPID
    let envar = mkEnVar pid (Just meth)
    -- set input arguments
    aftarg <- setArgs before meth args
    -- trigger task
    afttag <- ctxInsTrans' aftarg $ I.TranStat $ envar I.=: I.true
    -- pause and wait for task to complete
    aftwait <- ctxPause afttag (mkWaitForTask pid meth) (I.ActStat st)
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
    foldM (\loc' (farg,aarg) -> do aarg' <- exprToIExprDet aarg
                                   let t = mkType $ Type (ScopeTemplate tmMain) (tspec farg)
                                   ctxInsTransMany' loc' $ map I.TranStat
                                                         $ zipWith I.SAssign (I.exprScalars aarg' t) 
                                                                             (I.exprScalars (mkVar (Just pid) (Just meth) farg) t)) loc $ 
          filter (\(a,_) -> argDir a == ArgOut) $ zip (methArg meth) args

----------------------------------------------------------
-- Top-level function: convert process statement to CFA
----------------------------------------------------------

procStatToCFA :: (?spec::Spec, ?procs::[I.Process]) => Bool -> Statement -> I.Loc -> State CFACtx I.Loc
procStatToCFA cont stat before = do
    let ?cont=cont
    after <- statToCFA before stat
    modify (\ctx -> ctx {ctxCFA = I.cfaAddNullPtrTrans (ctxCFA ctx)})
    return after
