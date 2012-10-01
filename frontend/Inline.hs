{-# LANGUAGE ImplicitParams #-}

module Inline where

import Data.List
import Data.Maybe
import Control.Monad.State
import qualified Data.Map as M

import qualified ISpec as I
import Name
import NS
import Method
import Spec
import Template
import Process

-- Extract template from flattened spec (that only has one template)
tmMain :: (?spec::Spec) => Template
tmMain = head $ specTemplate ?spec


----------------------------------------------------------------------
-- Process ID (path in the process tree)
----------------------------------------------------------------------

data ProcTrans = ProcTrans { pPID    :: PID
                           , pBody   :: [I.Transition]
                           , pFinal  :: [I.Loc]  -- final locations
                           , pPCEnum :: I.Enumeration
                           }

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

mkVarName :: (WithName a) => Maybe PID -> Maybe Method -> a -> String
mkVarName mpid mmeth x = mkVarNameS mpid mmeth (sname x)

mkVarNameS :: Maybe PID -> Maybe Method -> String -> String
mkVarNameS mpid mmeth s = intercalate "/" names
    where names = fromMaybe [] mpid ++ 
                  [fromMaybe "" (fmap ((++ "()") . sname) mmeth)] ++ 
                  [s]

mkVar :: (WithName a) => Maybe PID -> Maybe Method -> a -> I.Expr
mkVar mpid mmeth x = I.EVar $ mkVarName mpid mmeth x

mkVarS :: Maybe PID -> Maybe Method -> String -> I.Expr
mkVarS mpid mmeth s = I.EVar $ mkVarNameS mpid mmeth s

mkVarDecl :: (WithName a, WithType a) => Maybe PID -> Maybe Method -> a -> I.Var
mkVarDecl mpid mmeth x = I.Var (mkVarName mpid mmeth x) (mkType $ typ x)

-- Variable that stores return value of a task
mkRetVar :: Maybe PID -> Method -> Maybe I.Expr
mkRetVar mpid meth = case methRettyp meth of
                          Nothing -> Nothing
                          Just _  -> Just $ mkVarS mpid (Just meth) "$ret"

mkRetVarDecl :: (?spec::Spec) => Maybe PID -> Method -> Maybe I.Var
mkRetVarDecl mpid meth = case methRettyp meth of
                              Nothing -> Nothing
                              Just t  -> Just $ I.Var (mkVarNameS mpid (Just meth) "$ret") 
                                                      (mkType $ Type (ScopeTemplate tmMain) t)

mkEnVarName :: PID -> Maybe Method -> String
mkEnVarName pid mmeth = mkVarNameS (Just pid) mmeth "$en"

mkEnVar :: PID -> Maybe Method -> I.Expr
mkEnVar pid mmeth = I.EVar $ mkEnVarName pid mmeth

mkEnVarDecl :: PID -> Maybe Method -> I.Var
mkEnVarDecl pid mmeth = I.Var (mkEnVarName pid mmeth) I.Bool

mkPCVarName :: PID -> String
mkPCVarName pid = mkVarNameS (Just pid) Nothing "$pc"

mkPCEnumName :: PID -> String
mkPCEnumName pid = mkVarNameS (Just pid) Nothing "$pcenum"

mkPCVar :: PID -> I.Expr
mkPCVar pid = I.EVar $ mkPCVarName pid

mkPCEnum :: PID -> I.Loc -> String
mkPCEnum pid loc = mkVarNameS (Just pid) Nothing $ show loc

mkPC :: PID -> I.Loc -> I.Expr
mkPC pid loc = I.EVar $ mkVarNameS (Just pid) Nothing ("$" ++ show loc)

--mkPCVarDecl :: Maybe PID -> Maybe Method -> 
--mkPCVarDecl (Just pid) Nothing


mkTagVarName :: String
mkTagVarName = "$tag"

mkTagVar :: I.Expr
mkTagVar = I.EVar mkTagVarName

mkTagVarDecl :: (?spec::Spec) => (I.Var, I.Enumeration)
mkTagVarDecl = (I.Var mkTagVarName (I.Enum "$tags"), I.Enumeration "$tags" tags)
    where tags = "$idle" :
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
mkContVarDecl = I.Var mkContVarName I.Bool

mkMagicVarName :: String
mkMagicVarName = "$magic"

mkMagicVar :: I.Expr
mkMagicVar = I.EVar mkMagicVarName

mkMagicVarDecl :: I.Var
mkMagicVarDecl = I.Var mkMagicVarName I.Bool

mkLoc :: Maybe PID -> Maybe Method -> I.Loc -> I.Expr
mkLoc mpid mmeth loc = I.EConst $ I.EnumVal $ mkVarNameS mpid mmeth (show loc)

type NameMap = M.Map Ident I.Expr

methodLMap :: PID -> Method -> NameMap 
methodLMap pid meth = 
    M.fromList $ map (\v -> (name v, mkVar (Just pid) (Just meth) v)) (methVar meth) ++
                 map (\a -> (name a, mkVar (Just pid) (Just meth) a)) (methArg meth)

procLMap :: PID -> Process -> NameMap
procLMap pid p = M.fromList $ map (\v -> (name v, mkVar (Just pid) Nothing v)) (procVar p)

globalNMap :: (?spec::Spec) => NameMap
globalNMap = error $ "Not implemented: globalNMap"
             -- global variables
             -- wires
             -- enums
             -- consts

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------

mkType :: Type -> I.Type
mkType t = error "Not implemented: mkType"


-----------------------------------------------------------
-- State maintained during CFA construction
-----------------------------------------------------------

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
ctxInsLoc = ctxInsLocLab I.LNone

ctxInsLocLab :: I.LocLabel -> State CFACtx I.Loc
ctxInsLocLab lab = do
    ctx <- get
    let (cfa', loc) = I.cfaInsLoc lab $ ctxCFA ctx
    put $ ctx {ctxCFA = cfa'}
    return loc


--ctxLabelLoc :: I.Loc -> I.LocLabel -> State CFACtx ()
--ctxLabelLoc loc lab = modify $ (\ctx -> ctx {ctxCFA = I.cfaLabelLoc loc lab $ ctxCFA ctx})

ctxInsTrans :: I.Loc -> I.Loc -> I.Statement -> State CFACtx ()
ctxInsTrans from to stat = modify $ (\ctx -> ctx {ctxCFA = I.cfaInsTrans from to stat $ ctxCFA ctx})

ctxInsTrans' :: I.Loc -> I.Statement -> State CFACtx I.Loc
ctxInsTrans' from stat = do
    to <- ctxInsLoc
    ctxInsTrans from to stat
    return to

ctxPause :: I.Loc -> State CFACtx I.Loc
ctxPause loc = do after <- ctxInsLocLab I.LPause
                  ctxInsTrans loc after I.nop
                  return after

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
