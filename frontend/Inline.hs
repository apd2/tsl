{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module Inline where

import Data.List
import Data.List.Split
import Data.Maybe
import Data.Tuple.Select
import Control.Monad.State
import qualified Data.Map             as M
import qualified Data.Graph.Inductive as G

import Util hiding (name)
import qualified IExpr    as I
import qualified CFA      as I
import qualified IType    as I
import qualified IVar     as I
import PID
import Name
import NS
import Method
import Spec
import Template
import Process
import Type
import TypeOps
import ExprOps
import Ops

-- Extract template from flattened spec (that only has one template)
tmMain :: (?spec::Spec) => Template
tmMain = head $ specTemplate ?spec

----------------------------------------------------------------------
-- Names
----------------------------------------------------------------------

mkVarName :: (WithName a) => NSID -> a -> String
mkVarName nsid x = mkVarNameS nsid (sname x)

mkVarNameS :: NSID -> String -> String
mkVarNameS (NSID mpid mmeth) s = intercalate "/" names
    where -- don't prefix function and procedure variables with PID
          mpid' = case mmeth of
                       Nothing -> mpid
                       Just m  -> case methCat m of
                                       Function  -> Nothing
                                       Procedure -> Nothing
                                       _         -> mpid
          names = maybe [] (return . show)              mpid' ++ 
                  maybe [] (return . (++ "()") . sname) mmeth ++ 
                  [s]

mkVar :: (WithName a) => NSID -> a -> I.Expr
mkVar nsid x = I.EVar $ mkVarName nsid x

mkVarS :: NSID -> String -> I.Expr
mkVarS nsid s = I.EVar $ mkVarNameS nsid s

mkVarDecl :: (?spec::Spec, WithName a, WithType a) => Bool -> NSID -> a -> I.Var
mkVarDecl mem nsid x = I.Var mem I.VarState (mkVarName nsid x) (mkType $ typ x)

parseVarName :: String -> (Maybe PrID, Maybe String, String)
parseVarName n = (mpid, mmeth, vname)
    where toks = splitOn "/" n
          vname = last toks
          (mpid,mmeth) = case init toks of
                              []    -> (Nothing, Nothing)
                              toks' -> (mp, mm)
                                       where
                                       mm = if (take 2 $ reverse $ last toks') == ")("
                                               then Just $ init $ init $ last toks'
                                               else Nothing
                                       mp = case init toks' of
                                                 []     -> Nothing
                                                 (p:ps) -> Just $ PrID p ps

-- Variable that stores return value of a task
mkRetVar :: Maybe PrID -> Method -> Maybe I.Expr
mkRetVar mpid meth = case methRettyp meth of
                          Nothing -> Nothing
                          Just _  -> Just $ mkVarS (NSID mpid (Just meth)) "$ret"

mkRetVarDecl :: (?spec::Spec) => Maybe PrID -> Method -> Maybe I.Var
mkRetVarDecl mpid meth = case methRettyp meth of
                              Nothing -> Nothing
                              Just t  -> Just $ I.Var False
                                                      I.VarState
                                                      (mkVarNameS (NSID mpid (Just meth)) "$ret") 
                                                      (mkType $ Type (ScopeTemplate tmMain) t)

mkEnVarName :: PrID -> Maybe Method -> String
mkEnVarName pid mmeth = mkVarNameS (NSID (Just pid) mmeth) "$en"

mkEnVar :: PrID -> Maybe Method -> I.Expr
mkEnVar pid mmeth = I.EVar $ mkEnVarName pid mmeth

mkEnVarDecl :: PrID -> Maybe Method -> I.Var
mkEnVarDecl pid mmeth = I.Var False I.VarState (mkEnVarName pid mmeth) I.Bool

mkWaitForTask :: PrID -> Method -> I.Expr
mkWaitForTask pid meth = envar I.=== I.false
    where envar = mkEnVar pid (Just meth)

isWaitForTask :: I.Expr -> Maybe String
isWaitForTask (I.EBinOp Eq (I.EVar n) e2) | e2 == I.false = 
    case parseVarName n of
         (_, ms, "$en") -> ms
         _              -> Nothing
isWaitForTask _ = Nothing

isWaitForMagic :: I.Expr -> Bool
isWaitForMagic (I.EBinOp Eq (I.EVar n) e2) | (e2 == I.false) && (n == mkMagicVarName) = True
                                           | otherwise = False
isWaitForMagic _ = False

mkPCVarName :: CID -> String
mkPCVarName cid = mkVarNameS (cid2nsid cid) "$pc"

mkPCEnumName :: CID -> String
mkPCEnumName cid = filter (\c -> notElem c "()")
                   $ mkVarNameS (cid2nsid cid) "$pcenum"

mkPCVar :: CID -> I.Expr
mkPCVar cid = I.EVar $ mkPCVarName cid

mkPCEnum :: CID -> I.Loc -> String
mkPCEnum cid loc = mkVarNameS (cid2nsid cid) $ "$pc" ++ show loc

mkPC :: CID -> I.Loc -> I.Expr
mkPC cid loc = I.EConst $ I.EnumVal $ mkPCEnum cid loc 

pcEnumToLoc :: String -> I.Loc
pcEnumToLoc str = read 
                  $ drop (length "$pc") 
                  $ fromJust $ find (isPrefixOf "$pc")
                  $ reverse 
                  $ tails str

-- PID of the last process to make a transition
mkEPIDVarName :: String
mkEPIDVarName = "$epid"

mkEPIDVar :: I.Expr
mkEPIDVar = I.EVar mkEPIDVarName

mkEPIDLVarName :: String
mkEPIDLVarName = "$lepid"

mkEPIDLVar :: I.Expr
mkEPIDLVar = I.EVar mkEPIDLVarName

mkEPIDEnumeratorName :: EPID -> String
mkEPIDEnumeratorName epid = "$" ++ show epid

parseEPIDEnumerator :: Spec -> String -> EPID
parseEPIDEnumerator spec n = parseEPID spec $ tail n

mkEPIDEnum :: EPID -> I.Expr
mkEPIDEnum = I.EConst . I.EnumVal . mkEPIDEnumeratorName

mkEPIDEnumName :: String
mkEPIDEnumName = "$epidenum" 

mkEPIDVarDecl :: [EPID] -> (I.Var, I.Enumeration)
mkEPIDVarDecl epids = (I.Var False I.VarState mkEPIDVarName (I.Enum mkEPIDEnumName), enum)
    where enum = I.Enumeration mkEPIDEnumName $ map mkEPIDEnumeratorName epids

mkEPIDLVarDecl :: I.Var
mkEPIDLVarDecl = I.Var False I.VarTmp mkEPIDLVarName (I.Enum mkEPIDEnumName)

mkTagVarName :: String
mkTagVarName = "$tag"

mkTagVar :: I.Expr
mkTagVar = I.EVar mkTagVarName

mkTagIdle = "$idle"

mkTagVarDecl :: (?spec::Spec) => (I.Var, I.Enumeration)
mkTagVarDecl = (I.Var False I.VarState mkTagVarName (I.Enum "$tags"), I.Enumeration "$tags" tags)
    where tags = mkTagIdle :
                 (map sname
                      $ filter ((== Task Controllable) . methCat)
                      $ tmMethod tmMain)
                              

tagMethod :: Method -> I.Expr
tagMethod meth = I.EConst $ I.EnumVal $ (sname $methName meth) 

tagIdle :: I.Expr
tagIdle = I.EConst $ I.EnumVal "$idle"

mkContVarName :: String
mkContVarName = "$cont"

mkContVar :: I.Expr
mkContVar = I.EVar mkContVarName

mkContVarDecl :: (?spec::Spec) => I.Var
mkContVarDecl = I.Var False I.VarState mkContVarName I.Bool

mkContLVarName :: String
mkContLVarName = "$lcont"

mkContLVar :: I.Expr
mkContLVar = I.EVar mkContLVarName

mkContLVarDecl :: (?spec::Spec) => I.Var
mkContLVarDecl = I.Var False I.VarTmp mkContLVarName I.Bool

mkMagicVarName :: String
mkMagicVarName = "$magic"

mkMagicVar :: I.Expr
mkMagicVar = I.EVar mkMagicVarName

mkMagicVarDecl :: I.Var
mkMagicVarDecl = I.Var False I.VarState mkMagicVarName I.Bool

mkMagicDoneCond :: I.Expr
mkMagicDoneCond = mkMagicVar I.=== I.false

mkErrVarName :: String
mkErrVarName = I.cfaErrVarName

mkErrVar :: I.Expr
mkErrVar = I.EVar mkErrVarName

mkErrVarDecl :: I.Var
mkErrVarDecl = I.Var False I.VarState mkErrVarName I.Bool

mkChoiceTypeName :: Int -> String
mkChoiceTypeName n = "$choice" ++ show n

mkChoiceType :: Int -> I.Type
mkChoiceType n = I.Enum $ mkChoiceTypeName n

mkChoiceValName :: String -> Int -> String
mkChoiceValName tname i = tname ++ "_" ++ show i

mkChoice :: I.Var -> Int -> I.Expr
mkChoice v i = I.EConst $ I.EnumVal $ mkChoiceValName tname i
    where I.Enum tname = I.varType v 

mkChoiceEnumDecl :: Int -> I.Enumeration
mkChoiceEnumDecl i = I.Enumeration {..}
    where enumName  = mkChoiceTypeName i
          enumEnums = map (mkChoiceValName enumName) [0..i-1]

type NameMap = M.Map Ident I.Expr

methodLMap :: Maybe PrID -> Method -> NameMap 
methodLMap mpid meth = 
    M.fromList $ map (\v -> (name v, mkVar (NSID mpid (Just meth)) v)) (methVar meth) ++
                 map (\a -> (name a, mkVar (NSID mpid (Just meth)) a)) (methArg meth)

procLMap :: Process -> NameMap
procLMap p = M.fromList $ map (\v -> (name v, mkVar (NSID (Just $ PrID (sname p) []) Nothing) v)) (procVar p)

scopeLMap :: Maybe PrID -> Scope -> NameMap
scopeLMap mpid sc = 
    case sc of
         ScopeMethod   _ meth -> methodLMap mpid meth
         ScopeProcess  _ proc -> procLMap proc
         ScopeTemplate _      -> M.empty
         
globalNMap :: (?spec::Spec) => NameMap
globalNMap = M.fromList $ gvars ++ wires ++ enums
    where -- global variables
          gvars  = map (\v -> (name v, mkVar (NSID Nothing Nothing) v)) $ tmVar tmMain
          -- wires
          wires  = map (\w -> (name w, mkVar (NSID Nothing Nothing) w)) $ tmWire tmMain
          -- enums
          enums  = concatMap (\d -> case tspec d of
                                            EnumSpec _ es -> map (\e -> (name e, I.EConst $ I.EnumVal $ sname e)) es
                                            _             -> []) 
                             $ specType ?spec
--          -- consts
--          consts = let ?scope = ScopeTop
--                   in mapMaybe (\c -> case constVal c of
--                                           Just (StructVal _) -> Nothing
--                                           v                  -> (name c, I.EConst $ mkVal $ val $ eval v))
--                          $ specConst ?spec

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------

mkType :: (?spec::Spec) => Type -> I.Type
mkType t = 
    case typ' t of
         Type _ (BoolSpec   _)      -> I.Bool
         Type _ (SIntSpec   _ w)    -> I.SInt w
         Type _ (UIntSpec   _ w)    -> I.UInt w
         Type s (StructSpec _ fs)   -> I.Struct $ map (\(Field _ t' n) -> I.Field (sname n) (mkType (Type s t'))) fs 
         Type _ (EnumSpec   _ es)   -> I.Enum $ getEnumName $ name $ head es
         Type s (PtrSpec    _ t')   -> I.Ptr $ mkType $ Type s t'
         Type s (ArraySpec  _ t' l) -> let ?scope = s in I.Array (mkType $ Type s t') (fromInteger $ evalInt l)
         Type _ t'                  -> error $ "mkType: " ++ show t'


getEnumName :: (?spec::Spec) => Ident -> String
getEnumName n = 
    sname $ fromJustMsg ("getEnumName: enumerator " ++ sname n ++ " not found") $
    find (\d -> case tspec d of
                     EnumSpec _ es -> isJust $ find ((==n) . name) es
                     _             -> False) 
         $ specType ?spec

-----------------------------------------------------------
-- State maintained during CFA construction
-----------------------------------------------------------

data CFACtx = CFACtx { ctxCID     :: Maybe CID                               -- ID of the CFA being constructed or Nothing if the CFA is not part of the final spec
                     , ctxStack   :: [(Scope, I.Loc, Maybe I.Expr, NameMap)] -- stack of syntactic scopes: (scope, return location, LHS, local namemap)
                     , ctxCFA     :: I.CFA                                   -- CFA constructed so far
                     , ctxBrkLocs :: [I.Loc]                                 -- stack break location
                     , ctxGNMap   :: NameMap                                 -- global variables visible in current scope
                     , ctxLastVar :: Int                                     -- counter used to generate unique variable names
                     , ctxVar     :: [I.Var]                                 -- temporary vars
                     }

ctxScope :: CFACtx -> Scope
ctxScope = sel1 . head . ctxStack

ctxRetLoc :: CFACtx -> I.Loc
ctxRetLoc = sel2 . head . ctxStack

ctxLHS :: CFACtx -> Maybe I.Expr
ctxLHS = sel3 . head . ctxStack

ctxLNMap :: CFACtx -> NameMap
ctxLNMap = sel4 . head . ctxStack

ctxPushScope :: Scope -> I.Loc -> Maybe I.Expr -> NameMap -> State CFACtx ()
ctxPushScope sc retloc lhs nmap = modify (\ctx -> ctx {ctxStack = (sc, retloc, lhs, nmap) : (ctxStack ctx)})

ctxPopScope :: State CFACtx ()
ctxPopScope = modify (\ctx -> ctx {ctxStack = tail $ ctxStack ctx})

ctxBrkLoc :: CFACtx -> I.Loc
ctxBrkLoc = head . ctxBrkLocs

ctxPushBrkLoc :: I.Loc -> State CFACtx ()
ctxPushBrkLoc loc = modify (\ctx -> ctx {ctxBrkLocs = loc : (ctxBrkLocs ctx)})

ctxPopBrkLoc :: State CFACtx ()
ctxPopBrkLoc = modify (\ctx -> ctx {ctxBrkLocs = tail $ ctxBrkLocs ctx})

ctxInsLoc :: State CFACtx I.Loc
ctxInsLoc = ctxInsLocLab (I.LInst I.ActNone)

ctxInsLocLab :: I.LocLabel -> State CFACtx I.Loc
ctxInsLocLab lab = do
    ctx <- get
    let (cfa', loc) = I.cfaInsLoc lab $ ctxCFA ctx
    put $ ctx {ctxCFA = cfa'}
    return loc

ctxLocSetAct :: I.Loc -> I.LocAction -> State CFACtx ()
ctxLocSetAct loc act = modify (\ctx -> ctx {ctxCFA = I.cfaLocSetAct loc act $ ctxCFA ctx})

ctxLocSetStack :: I.Loc -> I.Stack -> State CFACtx ()
ctxLocSetStack loc stack = modify (\ctx -> ctx {ctxCFA = I.cfaLocSetStack loc stack $ ctxCFA ctx})


ctxInsTrans :: I.Loc -> I.Loc -> I.TranLabel -> State CFACtx ()
ctxInsTrans from to t = modify (\ctx -> ctx {ctxCFA = I.cfaInsTrans from to t $ ctxCFA ctx})

ctxInsTransMany :: I.Loc -> I.Loc -> [I.TranLabel] -> State CFACtx ()
ctxInsTransMany from to ts = modify $ (\ctx -> ctx {ctxCFA = I.cfaInsTransMany from to ts $ ctxCFA ctx})

ctxInsTrans' :: I.Loc -> I.TranLabel -> State CFACtx I.Loc
ctxInsTrans' from t = do
    to <- ctxInsLoc
    ctxInsTrans from to t
    return to

ctxInsTransMany' :: I.Loc -> [I.TranLabel] -> State CFACtx I.Loc
ctxInsTransMany' from ts = do
    to <- ctxInsLoc
    ctxInsTransMany from to ts
    return to

ctxInsTmpVar :: I.Type -> State CFACtx I.Var
ctxInsTmpVar t = do
    lst  <- gets ctxLastVar
    mcid <- gets ctxCID
    sc   <- gets ctxScope
    let nsid = maybe (NSID Nothing Nothing) (\cid -> epid2nsid (cid2epid cid) sc) mcid
        vname = mkVarNameS nsid ("$tmp" ++ show (lst + 1))
        v = I.Var False I.VarTmp vname t
    modify $ (\ctx -> ctx { ctxLastVar = lst + 1
                          , ctxVar     = v:(ctxVar ctx)})
    return v

ctxFrames :: I.Loc -> State CFACtx I.Stack
ctxFrames loc = do
    cfastack <- gets ctxStack
    -- CFACtx stack stores return locations in stack frames,  but the Stack 
    -- type stores current locations in frames.  Shift ret locations by one 
    -- and append current location in the end. 
    let scopes = map sel1 cfastack
        locs   = (tail $ map sel2 cfastack) ++ [loc]
    return $ map (uncurry I.Frame) $ zip scopes locs


ctxPause :: I.Loc -> I.Expr -> I.LocAction -> State CFACtx I.Loc
ctxPause loc cond act = do
    after <- ctxInsLocLab (I.LPause act [] cond)
    stack <- ctxFrames after
    ctxLocSetStack after stack
    ctxSuffix loc after after
    ctxInsTrans' after (I.TranStat $ I.SAssume cond)

ctxFinal :: I.Loc -> State CFACtx I.Loc
ctxFinal loc = do 
    after <- ctxInsLocLab (I.LFinal I.ActNone [])
    stack <- ctxFrames after
    ctxLocSetStack after stack
    ctxSuffix loc after after
    return after

-- common code of ctxPause, ctxFinal, ctxErrTrans
ctxSuffix :: I.Loc -> I.Loc -> I.Loc -> State CFACtx ()
ctxSuffix loc after pc = do mcid  <- gets ctxCID
                            let mepid = fmap cid2epid mcid
                            -- set PID variable
                            aftepid <- if isNothing mepid
                                          then ctxInsTrans' loc $ I.TranNop
                                          else do befepid <- ctxInsTrans' loc $ I.TranStat $ I.SAssume $ mkEPIDLVar I.=== (mkEPIDEnum $ fromJust mepid)
                                                  ctxInsTrans' befepid $ I.TranStat $ mkEPIDVar I.=: mkEPIDLVar
                            -- 1. update PC
                            -- 2. uncontrollable transitions are only available in uncontrollable states
                            -- 3. non-deterministically set $cont to true if inside a magic block
                            if (isJust mcid && mepid /= Just EPIDCont) 
                               then do let Just cid = mcid
                                       aftpc    <- ctxInsTrans' aftepid $ I.TranStat  $ mkPCVar cid I.=: mkPC cid pc
                                       aftucont <- ctxInsTrans' aftpc $ I.TranStat    $ I.SAssume $ mkContVar I.=== I.false
                                       ifmagic  <- ctxInsTrans' aftucont $ I.TranStat $ I.SAssume $ mkMagicVar I.=== I.true
                                       ctxInsTrans ifmagic after $ I.TranStat         $ mkContVar I.=: mkContLVar
                                       ctxInsTrans aftucont after $ I.TranStat        $ I.SAssume $ mkMagicVar I.=== I.false
                               else ctxInsTrans aftepid after I.TranNop

ctxErrTrans :: I.Loc -> State CFACtx ()
ctxErrTrans loc = do
    aftsuf <- ctxInsLoc
    ctxSuffix loc aftsuf I.cfaErrLoc
    modify $ \ctx -> ctx {ctxCFA = I.cfaErrTrans aftsuf $ ctxCFA ctx}

-- Add error transitions for all potential null-pointer dereferences
ctxAddNullPtrTrans :: State CFACtx ()
ctxAddNullPtrTrans = do 
    ctx  <- get
    _ <- mapM addNullPtrTrans1 (G.labEdges $ ctxCFA ctx)
    return () 

addNullPtrTrans1 :: (I.Loc,I.Loc,I.TranLabel) -> State CFACtx ()
addNullPtrTrans1 (from , to, l@(I.TranStat (I.SAssign e1 e2))) = do
    let cond = -- We don't have access to ?spec here, hence cannot determine type of
               -- NullVal.  Keep it undefined until a separate pass.
               I.disj 
               $ map (\e -> e I.=== (I.EConst $ I.NullVal $ error "NullVal type undefined")) 
               $ I.exprPtrSubexpr e1 ++ I.exprPtrSubexpr e2
    case cond of
         I.EConst (I.BoolVal False) -> return ()
         _ -> do modify $ \ctx -> ctx {ctxCFA = G.delLEdge (from, to, l) $ ctxCFA ctx}
                 fromok  <- ctxInsTrans' from (I.TranStat $ I.SAssume $ I.neg cond)
                 fromerr <- ctxInsTrans' from (I.TranStat $ I.SAssume cond)
                 ctxInsTrans fromok to l
                 ctxErrTrans fromerr
   
addNullPtrTrans1 (_    , _, _)                             = return ()



ctxPruneUnreachable :: State CFACtx ()
ctxPruneUnreachable = modify (\ctx -> ctx {ctxCFA = I.cfaPruneUnreachable (ctxCFA ctx) [I.cfaInitLoc]})

