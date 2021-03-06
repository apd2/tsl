{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards, ScopedTypeVariables #-}

-- Convert flattened spec to internal representation
module Frontend.SpecInline (specSimplify, spec2Internal, specXducers2Internal) where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State hiding (guard)
import qualified Data.Graph.Inductive.Graph as G

import TSLUtil
import Util hiding (name, trace)
import Frontend.Spec
import qualified Internal.ISpec       as I
import qualified Internal.TranSpec    as I
import qualified Internal.IExpr       as I
import qualified Internal.CFA         as I
import qualified Internal.IType       as I
import qualified Internal.IVar        as I
import qualified Internal.ITransducer as I
import Internal.PID
import Pos
import Name
import Frontend.NS
import Frontend.Statement
import Frontend.StatementInline
import Frontend.Expr
import Frontend.ExprInline
import Frontend.Template
import Frontend.TemplateOps
import Frontend.TemplateFlatten
import Frontend.RelationInline
import Frontend.TVar
import Frontend.TVarOps
import Frontend.Method
import Frontend.MethodOps
import Frontend.Process
import Frontend.Type
import Frontend.Inline
import Frontend.Transducer


-- Main function
-- The input spec must be simplified using specSimplify
spec2Internal :: Spec -> I.Spec
spec2Internal s = 
    let -- preprocessing
        ?spec = s in
    let cfas = I.specAllCFAs spec
        pids = map fst $ I.specAllProcs spec
        -- PC variables and associated enums
        (pcvars, pcenums) = unzip 
                            $ map (\(EPIDProc pid,cfa) -> let enum = I.Enumeration (mkPCEnumName pid) $ map (mkPCEnum pid) $ I.cfaDelayLocs cfa
                                                              var  = I.Var False I.VarState (mkPCVarName pid) (I.Enum Nothing $ I.enumName enum)
                                                          in (var, enum)) 
                            $ filter ((/=1) . length . I.cfaDelayLocs . snd)
                            $ filter ((/= EPIDCont) . fst) cfas
        -- built-in enums used in translating choice{} statements
        nctasks = length $ filter ((== Task Controllable) . methCat) $ tmMethod tmMain
        choiceenum = map mkChoiceEnumDecl [0..(max 31 nctasks)]
        senum = mapMaybe (\d -> case tspec d of
                                     EnumSpec _ es -> Just $ I.Enumeration (sname d) (map sname es)
                                     _             -> Nothing) (specType ?spec)                                                     
        (pidlvar, pidenum)  = mkPIDLVarDecl pids
        vars                = mkVars
        (tvar, tenum)       = mkTagVarDecl
        fairreg = mkFair spec'
        ((specWire, specPrefix, inittran, goals), (_, extratmvars)) =  
            runState (do wire      <- mkWires
                         prefix    <- mkPrefix
                         inittr    <- mkInit
                         usergoals <- mapM mkGoal $ tmGoal tmMain
                         maggoal   <- mkMagicGoal
                         return (wire, prefix, inittr, maggoal:usergoals))
                     (0,[])
        extraivars = let ?scope = ScopeTemplate tmMain in map (\v -> mkVarDecl (varMem v) (NSID Nothing Nothing) v (varType v)) extratmvars
        (specProc, tmppvs) = unzip $ (map procToCProc $ tmProcess tmMain) 
        specRels           = map relToIRel $ tmRelation tmMain
        specEnum           = choiceenum ++ (tenum : pidenum : (senum ++ pcenums))
        specVar            = cvars ++ [tvar, pidlvar] ++ pcvars ++ vars ++ concat tmppvs ++ extraivars
        specCAct           = ctran
        specTran           = error "specTran undefined"
        specUpds           = M.empty -- mkUpds spec'
        specApply          = map applyToIApply $ tmApply tmMain
        specXducers        = map xducerToIXducer $ specTransducer s
        spec0              = I.Spec {..}
        spec               = I.specMapCFA (\cfa -> I.cfaMapExpr cfa $ exprExpandLabels spec0) spec0
        spec'              = I.specMapCFA (\cfa -> I.cfaMapStat cfa $ statAddNullTypes spec) spec

        -- Controllable transitions
        (ctran, cvars)     = mkCTran 
        -- Uncontrollable transitions
        utran = concatMap (\(epid, cfa) -> cfaToITransitions epid cfa) 
                          $ filter ((/= EPIDCont) . fst)
                          $ I.specAllCFAs spec'
        -- initialise PC variables.
        pcinit = map (\(EPIDProc pid, cfa) -> mkPCEq cfa pid (mkPC pid I.cfaInitLoc)) 
                 $ filter ((/= EPIDCont) . fst) 
                 $ I.specAllCFAs spec'
        -- initialise $en vars to false
        peninit = concatMap (mapPTreeFProc (\pid _ -> mkEnVar pid Nothing  I.=== I.false)) $ tmProcess tmMain
        maginit  = mkMagicVar I.=== I.false
        errinit  = mkErrVar   I.=== I.false 

        res = 
         spec' {I.specTran = I.TranSpec { I.tsCTran  = cfaToITransitions EPIDCont $ I.specCAct spec'
                                        , I.tsUTran  = utran
                                        , I.tsInit   = (inittran, I.conj $ (pcinit ++ peninit ++ [errinit, maginit]))
                                        , I.tsGoal   = map (\g -> g{I.goalCond = (I.goalCond g){I.tranCFA = I.cfaMapExpr (I.tranCFA $ I.goalCond g) $ exprExpandLabels spec'}}) goals
                                        , I.tsFair   = map (\f -> f{I.fairCond = exprExpandLabels spec' (I.fairCond f)}) fairreg
                                        }} in
       {-I.cfaTraceFiles (zip (map (("tr" ++) . show) [0..]) $ map I.tranCFA $ (I.tsUTran $ I.specTran res) ++ (I.tsCTran $ I.specTran res)) $-} res
      
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
mkWires :: (?spec::Spec) => NameGen (Maybe I.CFA)
mkWires | (null $ tmWire tmMain) = return Nothing
        | otherwise              = do
    let wires = orderWires
        -- Generate assignment statement for each wire
    stat <- let ?scope = ScopeTemplate tmMain
            in statSimplify $ SSeq nopos Nothing $ map (\w -> SAssign (pos w) Nothing (ETerm nopos [name w]) (fromJust $ wireRHS w)) wires
    let ctx = CFACtx { ctxEPID    = Nothing
                     , ctxStack   = [(ScopeTemplate tmMain, error "return from a wire assignment", Nothing, M.empty)]
                     , ctxCFA     = I.newCFA (ScopeTemplate tmMain) stat I.true
                     , ctxBrkLocs = [error "break outside a loop"]
                     , ctxGNMap   = globalNMap
                     , ctxLastVar = 0
                     , ctxVar     = []
                     , ctxLabels  = []}
        ctx' = let ?procs =[] 
                   ?nestedmb = False 
                   ?xducer = False
               in execState (procStatToCFA stat I.cfaInitLoc) ctx
    return $ Just $ {-I.cfaTraceFile (ctxCFA ctx') "wires_cfa" $-} ctxCFA ctx'


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
-- Prefix-block
----------------------------------------------------------------------

-- Generate transition that performs all prefix actions.  It will be
-- implicitly prepended to all "regular" transitions.
mkPrefix :: (?spec::Spec) => NameGen (Maybe I.CFA)
mkPrefix | (null $ tmPrefix tmMain) = return Nothing
         | otherwise                = do
    stat <- let ?scope = ScopeTemplate tmMain
            in statSimplify $ SSeq nopos Nothing $ map prefBody $ tmPrefix tmMain
    let ctx = CFACtx { ctxEPID    = Nothing
                     , ctxStack   = [(ScopeTemplate tmMain, error "return from an prefix-block", Nothing, M.empty)]
                     , ctxCFA     = I.newCFA (ScopeTemplate tmMain) stat I.true
                     , ctxBrkLocs = [error "break outside a loop"]
                     , ctxGNMap   = globalNMap
                     , ctxLastVar = 0
                     , ctxVar     = []
                     , ctxLabels  = []}
        ctx' = let ?procs = [] 
                   ?nestedmb = False
                   ?xducer = False
               in execState (procStatToCFA stat I.cfaInitLoc) ctx
    return $ Just $ {- I.cfaTraceFile (ctxCFA ctx') "prefix_cfa" $-} ctxCFA ctx'

----------------------------------------------------------------------
-- Fair sets
----------------------------------------------------------------------

--mkFair :: (?spec::Spec) => I.Spec -> ([I.Var], [I.Expr], I.FairRegion)
--mkFair ispec = (mkFairRegVarDecls ispec
--               , map (I.=== I.false) $ mkFairRegVars ispec
--               , I.FairRegion "fair" $ I.neg $ I.conj $ mkFairRegVars ispec)

mkFair :: (?spec::Spec) => I.Spec -> [I.FairRegion]
mkFair ispec = mkFairSched : (map mkFairProc $ I.specAllProcs ispec)
    where 
    -- Fair scheduling:  GF (not ($magic==true && $cont == false))
    mkFairSched = I.FairRegion "fair_scheduler" $ (mkMagicVar I.=== I.true) `I.land` (mkContLVar I.=== I.false)

    -- For each uncontrollable process: 
    -- GF (not ((\/i . pc=si && condi) && lastpid /= pid))
    -- where si and condi are process pause locations and matching conditions
    -- i.e, the process eventually either becomes disabled or makes a transition.
    mkFairProc :: (PrID, I.Process) -> I.FairRegion
    mkFairProc (pid,p) = I.FairRegion ("fair_" ++ show pid)
                         $ mkFairCFA (I.procCFA p) pid 

    mkFairCFA :: I.CFA -> PrID -> I.Expr
    mkFairCFA cfa pid = 
        ((mkPIDLVar I./== mkPIDEnum pid) `I.lor` (mkContLVar I.=== I.true)) `I.land`
        (I.disj $ map (\loc -> mkPCEq cfa pid (mkPC pid loc) `I.land` (I.cfaLocWaitCond cfa loc)) 
                $ filter (not . I.isDeadendLoc cfa) 
                $ I.cfaDelayLocs cfa)


----------------------------------------------------------------------
-- Explicit update functions 
----------------------------------------------------------------------

--mkUpds :: I.Spec -> M.Map String [(I.Expr, I.Expr)]
--mkUpds spec = M.fromList $ []

--contUpd :: [(I.Expr, I.Expr)]
--contUpd = [ (        (I.neg mkContVar) `I.land` mkMagicVar , mkContLVar)
--          , ( I.neg ((I.neg mkContVar) `I.land` mkMagicVar), I.false)]

--epidUpd :: [(I.Expr, I.Expr)]
--epidUpd = [ (mkContLVar      , I.EConst $ I.EnumVal $ mkEPIDEnumeratorName EPIDCont)
--          , (I.neg mkContLVar, mkEPIDLVar)]


----------------------------------------------------------------------
-- Init and goal conditions
----------------------------------------------------------------------

mkInit :: (?spec::Spec) => NameGen I.Transition
mkInit = do 
    -- conjunction of initial variable assignments
    let ass = SSeq nopos Nothing
              $ mapMaybe (\v -> case varInit $ gvarVar v of
                                     Nothing -> Nothing
                                     Just e  -> Just $ SAssume (pos v) Nothing $ EBinOp (pos v) Eq (ETerm nopos $ [name v]) e) (tmVar tmMain)
        -- add init blocks
        cond = SAssume nopos Nothing $ eAnd nopos $ map initBody (tmInit tmMain)
    mkCond "$init" (SSeq nopos Nothing [ass, cond]) []

-- $err == false
noerror :: I.Expr
noerror = I.EUnOp Not mkErrVar

mkGoal :: (?spec::Spec) => Goal -> NameGen I.Goal
mkGoal g = -- Add $err==false to the goal condition
           (liftM $ I.Goal (sname g)) $ mkCond (sname g) (SAssume nopos Nothing $ goalCond g) [{-I.EUnOp Not mkMagicVar, noerror-}]

-- In addition to regular goals, we are required to be outside a magic block
-- infinitely often
mkMagicGoal :: (?spec::Spec) => NameGen I.Goal
mkMagicGoal = (liftM $ I.Goal "$magic_goal") $ mkCond "$magic_goal" (SAssume nopos Nothing $ EBool nopos True) [I.EUnOp Not mkMagicVar, noerror]

mkCond :: (?spec::Spec) => String -> Statement -> [I.Expr] -> NameGen I.Transition
mkCond descr s extra = do
    -- simplify and convert into a statement
    stat <- let ?scope = ScopeTemplate tmMain 
            in statSimplify s
    let ctx = CFACtx { ctxEPID    = Nothing
                     , ctxStack   = [(ScopeTemplate tmMain, error $ "return from " ++ descr, Nothing, M.empty)]
                     , ctxCFA     = I.newCFA (ScopeTemplate tmMain) stat I.true
                     , ctxBrkLocs = error "break outside a loop"
                     , ctxGNMap   = globalNMap
                     , ctxLastVar = 0
                     , ctxVar     = []
                     , ctxLabels  = []}
        ctx' = let ?procs = [] 
                   ?nestedmb = False
                   ?xducer = False
               in execState (do aft <- procStatToCFA stat I.cfaInitLoc
                                ctxPause aft I.true I.ActNone) ctx
        trans = map snd $ I.cfaLocTrans (ctxCFA ctx') I.cfaInitLoc
        -- precondition
    return $ case trans of
                  [t] -> let res = foldl' tranAppend (I.Transition (head $ I.cfaSource t) (head $ I.cfaSink t) t) (map I.SAssume extra)
                         in {-I.cfaTraceFile (I.tranCFA res) descr $-} res
                  _   -> error $ "mkCond " ++ show s ++ ": Invalid condition"

----------------------------------------------------------------------
-- Controllable transitions
----------------------------------------------------------------------

-- only allow controllable transitions in a controllable state
--contGuard = I.SAssume $ I.conj [mkContVar I.=== I.true]
--contGuard = I.SAssume $ I.conj $ [mkMagicVar I.=== I.true, mkContVar I.=== 
--I.true]

-- generate CFA that represents all possible controllable transitions
mkCTran :: (?spec::Spec) => (I.CFA, [I.Var])
mkCTran =  I.cfaTraceFile (ctxCFA ctx' ) "cont_cfa" $ (ctxCFA ctx', ctxVar ctx')
    where sc   = ScopeTemplate tmMain
          ctasks = filter ((== Task Controllable) . methCat) $ tmMethod tmMain
          stats = SMagExit nopos Nothing : 
                  SDoNothing nopos Nothing :
                  (map (\m -> SInvoke nopos Nothing (MethodRef nopos [name m]) 
                              $ map (\a -> if' (argDir a == ArgIn) (Just $ ENonDet nopos (Just $ Ident nopos $ mkArgTmpVarName m a)) Nothing) (methArg m))
                   ctasks)
          stats' = map (\stat -> let ?scope = sc in evalState (statSimplify stat) (0,[])) stats
          ctx  = CFACtx { ctxEPID    = Just EPIDCont
                        , ctxStack   = [(sc, error "return from controllable transition", Nothing, M.empty)]
                        , ctxCFA     = I.newCFA sc (SSeq nopos Nothing []) I.true
                        , ctxBrkLocs = []
                        , ctxGNMap   = globalNMap
                        , ctxLastVar = 0
                        , ctxVar     = []
                        , ctxLabels  = []}
          ctx' = let ?procs = []
                     ?nestedmb = False
                     ?xducer = False
                 in execState (mapM (\(t,s) -> do afttag <- ctxInsTrans' I.cfaInitLoc $ I.TranStat $ I.SAssume $ mkTagVar I.=== (I.EConst $ I.EnumVal t)
                                                  aftcont <- ctxInsTrans' afttag $ I.TranStat $ I.SAssume $ mkContLVar I.=== I.true
                                                  aftmag <- ctxInsTrans' aftcont $ I.TranStat $ I.SAssume $ mkMagicVar I.=== I.true
                                                  aftcall <- procStatToCFA s aftmag
                                                  ctxFinal aftcall) 
                                    $ zip mkTagList stats') ctx

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------

mkVars :: (?spec::Spec) => [I.Var]
mkVars = mkErrVarDecl : mkContLVarDecl : mkMagicVarDecl : (wires ++ gvars ++ fvars ++ ivars ++ fpvars ++ pvars)
    where
    -- global variables
    gvars = let ?scope = ScopeTemplate tmMain 
                in map (\v -> mkVarDecl (varMem $ gvarVar v) (NSID Nothing Nothing) (gvarVar v) (varType $ gvarVar v)) $ tmVar tmMain

    -- wires
    wires = let ?scope = ScopeTemplate tmMain 
                in map (\w -> mkVarDecl False (NSID Nothing Nothing) w (wireType w)) $ tmWire tmMain

    -- functions, procedures, and controllable tasks
    fvars = concatMap (methVars Nothing False)
                      $ filter ((flip elem) [Function, Procedure, Task Controllable] . methCat) 
                      $ tmMethod tmMain

    -- inlined uncontrollable and invisible tasks: 
    ivars = concatMap (concat . mapPTreeInlinedTask (\pid m -> methVars (Just pid) False m))
                      $ tmProcess tmMain

    -- For each root process:
    -- * local variables
    pvars = concatMap (\p -> map (\v -> let ?scope = ScopeProcess tmMain p 
                                        in mkVarDecl (varMem v) (NSID (Just $ PrID (sname p) []) Nothing) v (varType v)) (procVar p)) 
                      $ tmProcess tmMain

    -- For each forked process:
    -- * enabling variable
    fpvars = concatMap (mapPTreeFProc (\pid _ -> mkEnVarDecl pid Nothing))
                       $ tmProcess tmMain

    methVars :: Maybe PrID -> Bool -> Method -> [I.Var]
    methVars mpid ret m = 
        (let ?scope = ScopeMethod tmMain m in map (\v -> mkVarDecl (varMem v) (NSID mpid (Just m)) v (varType v)) (methVar m)) ++ 
        (let ?scope = ScopeMethod tmMain m in map (\a -> mkVarDecl False (NSID mpid (Just m)) a (argType a)) (methArg m)) ++
        (if ret then maybeToList (mkRetVarDecl mpid m) else [])

----------------------------------------------------------------------
-- Transducers
----------------------------------------------------------------------

specXducers2Internal :: Spec -> I.Spec
specXducers2Internal s = 
    let -- preprocessing
        ?spec = s in
    let specEnum    = mapMaybe (\d -> case tspec d of
                                           EnumSpec _ es -> Just $ I.Enumeration (sname d) (map sname es)
                                           _             -> Nothing) (specType ?spec)                                                     
        specXducers        = map xducerToIXducer $ specTransducer s
    in I.Spec {..}



xducerToIXducer :: (?spec::Spec) => Transducer -> I.Transducer
xducerToIXducer x@(Transducer _ n is os b) = I.Transducer (sname n) is' os' b'
    where is' = map (\i -> (mkType $ Type ScopeTop $ tpType i, sname i)) is
          os' = map (\o -> (mkType $ Type ScopeTop $ tpType o, sname o)) os
          sc = ScopeTransducer x
          ctx stat = CFACtx { ctxEPID    = Nothing 
                            , ctxStack   = [(sc, error "return from a transducer", Nothing, xducerLMap x)]
                            , ctxCFA     = I.newCFA sc stat I.true
                            , ctxBrkLocs = error "break outside a loop"
                            , ctxGNMap   = globalConstNMap
                            , ctxLastVar = 0
                            , ctxVar     = []
                            , ctxLabels  = []}
          reftoiref :: TxPortRef -> I.TxPortRef
          reftoiref (TxInputRef p)   = I.TxInputRef $ sname p
          reftoiref (TxLocalRef i p) = I.TxLocalRef (sname i) (sname p)
          b' = case b of
                    Left  (refs, insts) -> Left ( map reftoiref refs
                                                , map (\i -> I.TxInstance (sname $ tiTxName i) (sname $ tiInstName i) (map (fmap reftoiref) $ tiInputs i)) insts) 
                    Right st    -> let ?procs = []
                                       ?nestedmb = False 
                                       ?xducer = True in
                                   let stvars = map (\v -> I.Var False I.VarState (sname v) (mkType $ Type sc $ tspec v)) $ stmtVar st
                                       st' = let ?scope = sc in evalState (statSimplify st) (0,[])
                                       cfa = ctxCFA $ execState (do aft <- procStatToCFA st' I.cfaInitLoc
                                                                    ctxFinal aft) (ctx st')
                                   in Right (cfa, stvars)

----------------------------------------------------------------------
-- CFA transformation
----------------------------------------------------------------------

-- Convert normal or forked process to CFA
procToCFA :: (?spec::Spec, ?procs::[I.Process]) => PrID -> NameMap -> Scope -> Statement -> (I.CFA, [I.Var])
procToCFA pid@(PrID _ ps) lmap parscope stat =  {-I.cfaTraceFile (ctxCFA ctx') (show pid)-} (ctxCFA ctx', ctxVar ctx')
    where -- top-level processes are not guarded
          guarded = not $ null ps
          guard = if guarded 
                     then mkEnVar pid Nothing I.=== I.true
                     else I.true
          -- Add process-local variables to nmap
          ctx = CFACtx { ctxEPID    = Just $ EPIDProc pid 
                       , ctxStack   = [(parscope, error "return from a process", Nothing, lmap)]
                       , ctxCFA     = I.newCFA parscope stat guard
                       , ctxBrkLocs = error "break outside a loop"
                       , ctxGNMap   = globalNMap
                       , ctxLastVar = 0
                       , ctxVar     = []
                       , ctxLabels  = []}
          ctx' = execState (do aftguard <- if guarded
                                              then ctxInsTrans' I.cfaInitLoc $ I.TranStat $ I.SAssume guard
                                              else return I.cfaInitLoc
                               aft <- let ?nestedmb = False 
                                          ?xducer = False in 
                                      procStatToCFA stat aftguard
                               _   <- ctxFinal aft
                               modify $ \c -> c {ctxCFA = cfaShortcut $ ctxCFA c}
                               ctxUContInsertSuffixes
                               ctxPruneUnreachable) ctx

-- Shortcut initial transition of the CFA if it does not do anything
cfaShortcut :: I.CFA -> I.CFA
cfaShortcut cfa = cfaShortcut' cfa I.cfaInitLoc

cfaShortcut' :: I.CFA -> I.Loc -> I.CFA
cfaShortcut' cfa l | (I.isDelayLabel $ fromJust $ G.lab cfa l) && (l /= I.cfaInitLoc) = graphUpdNode I.cfaInitLoc (\lab -> lab {I.locStack = I.stackSetLoc (I.locStack lab) I.cfaInitLoc})
                                                                                        $ graphChangeNodeID l I.cfaInitLoc 
                                                                                        $ G.delNode I.cfaInitLoc cfa
                   | (length $ G.lsuc cfa l) /= 1                                     = cfa
                   | (snd $ head $ G.lsuc cfa l) /= I.TranNop                         = cfa
                   | otherwise                                                        = cfaShortcut' cfa $ head $ G.suc cfa l

-- Recursively construct CFA's for the process and its children
procToCProc :: (?spec::Spec) => Process -> (I.Process, [I.Var])
procToCProc p = fprocToCProc Nothing ((ScopeProcess tmMain p), (sname p, (procStatement p)))

fprocToCProc :: (?spec::Spec) => Maybe PrID -> (Scope, (String, Statement)) -> (I.Process, [I.Var])
fprocToCProc mparpid (sc, (n,stat)) = (I.Process{..}, pvs ++ concat cvs)
    where lmap                = scopeLMap mparpid sc 
          pid                 = maybe (PrID n []) (\parpid -> childPID parpid n) mparpid
          procName            = n
          (procChildren, cvs) = unzip $ map (fprocToCProc $ Just pid) $ forkedProcsRec sc stat
          (procCFA,pvs)       = let ?procs = procChildren in procToCFA pid lmap sc stat

-- Map a function over all inlined invisible and uncontrollable tasks called by the process
mapPTreeInlinedTask :: (?spec::Spec) => (PrID -> Method -> a) -> Process -> [a]
mapPTreeInlinedTask f p = mapPTreeInlinedTask' f (PrID (sname p) []) (ScopeProcess tmMain p) (procStatement p)

mapPTreeInlinedTask' :: (?spec::Spec) => (PrID -> Method -> a) -> PrID -> Scope -> Statement -> [a]
mapPTreeInlinedTask' f pid sc stat = 
    (map (f pid)
     $ filter (\m -> elem (methCat m) [Task Invisible, Task Uncontrollable])
     $ procCallees sc stat)
    ++
    (concatMap (\(sc',(n,st)) -> mapPTreeInlinedTask' f (childPID pid n) sc' st) $ forkedProcsRec sc stat)


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
procCallees' s (SSeq     _ _ ss)                  = concatMap (procCallees' s) ss
procCallees' s (SForever _ _ b)                   = procCallees' s b
procCallees' s (SDo      _ _ b _)                 = procCallees' s b
procCallees' s (SWhile   _ _ _ b)                 = procCallees' s b
procCallees' s (SFor     _ _ (i,_,u) b)           = (fromMaybe [] $ fmap (procCallees' s) i) ++ procCallees' s u ++ procCallees' s b
procCallees' s (SChoice  _ _ ss)                  = concatMap (procCallees' s) ss
procCallees' _ (SInvoke  _ _ mref _)              = [mref]
procCallees' _ (SAssign  _ _ _ (EApply _ mref _)) = [mref]
procCallees' s (SITE     _ _ _ t me)              = procCallees' s t ++ (fromMaybe [] $ fmap (procCallees' s) me)
procCallees' s (SCase    _ _ _ cs md)             = concatMap (\(_,st) -> procCallees' s st) cs ++
                                                    (fromMaybe [] $ fmap (procCallees' s) md)
procCallees' _ _                                  = []

procCalleesRec :: (?spec::Spec) => Scope -> Statement -> [MethodRef]
procCalleesRec s stat = ms1 ++ ms2
    where ms1 = procCallees' s stat
          ms2 = concatMap (procCalleesRec s . fromRight . methBody . snd . getMethod s) ms1

-- Find processes forked by the statement
forkedProcs :: (?spec::Spec) => Statement -> [(String, Statement)]
forkedProcs (SSeq _ _ ss)              = concatMap forkedProcs ss
forkedProcs (SPar _ _ ps)              = map (\st -> (sname $ fromJust $ stLab st, st)) ps
forkedProcs (SForever _ _ b)           = forkedProcs b
forkedProcs (SDo _ _ b _)              = forkedProcs b
forkedProcs (SWhile _ _ _ b)           = forkedProcs b
forkedProcs (SFor _ _ (minit, _, i) b) = fromMaybe [] (fmap forkedProcs minit) ++ forkedProcs i ++ forkedProcs b
forkedProcs (SChoice _ _ ss)           = concatMap forkedProcs ss
forkedProcs (SITE _ _ _ t me)          = forkedProcs t ++ fromMaybe [] (fmap forkedProcs me)
forkedProcs (SCase _ _ _ cs mdef)      = concatMap (forkedProcs . snd) cs ++
                                         fromMaybe [] (fmap forkedProcs mdef)
forkedProcs _                          = []

-- Recurse over task invocations
forkedProcsRec :: (?spec::Spec) => Scope -> Statement -> [(Scope, (String, Statement))]
forkedProcsRec s stat = 
    (map (s,) $ forkedProcs stat) ++
    (concatMap (\m -> map (ScopeMethod tmMain m,) $ forkedProcs $ fromRight $ methBody m) (procCallees s stat))

---------------------------------------------------------------
-- CFA to LTS transformation
---------------------------------------------------------------

--cfaToITransition :: I.CFA -> String -> I.Transition
--cfaToITransition cfa fname = case trans of
--                                  [t] -> {-I.cfaTraceFile (I.tranCFA t) fname $-} t
--                                  _   -> error $ "cfaToITransition: Invalid CFA:\n" ++ (intercalate "\n\n" $ map show trans)
--      where trans = locTrans cfa I.cfaInitLoc

-- Convert CFA to a list of transitions.
-- Assume that unreachable states have already been pruned.
cfaToITransitions :: EPID -> I.CFA -> [I.Transition]
cfaToITransitions epid cfa = {-I.cfaTraceFileMany (map I.tranCFA trans') ("tran_" ++ show epid)-} trans'
    where
    -- compute a set of transitions for each location labelled with pause or final
    states = I.cfaDelayLocs cfa
    trans = concatMap (I.cfaLocTrans cfa) states
    trans' = map (extractTransition epid cfa . snd) trans

-- Extract transition into a separate CFA
extractTransition :: EPID -> I.CFA -> I.CFA -> I.Transition
extractTransition epid cfa tcfa = 
    let from = head $ I.cfaSource tcfa
        to   = head $ I.cfaSink tcfa
    in case epid of 
            EPIDCont -> I.Transition from to tcfa
            EPIDProc pid -> -- check PC value before the transition
                            let (cfa2, befpc) = I.cfaInsLoc (I.LInst I.ActNone) tcfa
                                cfa3 = I.cfaInsTrans befpc from (I.TranStat $ I.SAssume $ mkPCEq cfa pid (mkPC pid from)) cfa2
                            in I.Transition befpc to cfa3

tranAppend :: I.Transition -> I.Statement -> I.Transition
tranAppend (I.Transition from to cfa) s = I.Transition from to' cfa'
    where (cfa', to') = I.cfaInsTrans' to (I.TranStat s) cfa

