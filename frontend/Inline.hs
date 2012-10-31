{-# LANGUAGE ImplicitParams #-}

module Inline where

import Data.List
import Data.Maybe
import Control.Monad.State
import qualified Data.Map as M
import Text.PrettyPrint

import PP
import Pos
import Util hiding (name)
import qualified ISpec as I
import qualified IExpr as I
import qualified CFA   as I
import qualified IType as I
import qualified IVar  as I
import Name
import NS
import Method
import Spec
import Template
import Process
import Type
import TypeOps
import ExprOps
import Const
import Val

-- Extract template from flattened spec (that only has one template)
tmMain :: (?spec::Spec) => Template
tmMain = head $ specTemplate ?spec


----------------------------------------------------------------------
-- Process ID (path in the process tree)
----------------------------------------------------------------------

data ProcTrans = ProcTrans { pPID    :: PID
                           , pBody   :: [I.Transition]
                           , pVar    :: [I.Var]
                           , pFinal  :: [I.Loc]            -- final locations
                           , pPCEnum :: I.Enumeration
                           , pPauses :: [(I.Loc, I.Expr)]  -- process locations and corresponding wait conditions
                           }

type PID = [String]

instance PP ProcTrans where
    pp p = text "ProcTrans" <+> (text $ pidToName $ pPID p) <+>
           (braces' $
           (vcat $ map (($+$ text "") . pp) (pBody p))
           $+$
           (vcat $ map (($+$ text "") . pp) (pVar p))
           $+$
           (text "final locations:" <+> (hsep $ punctuate comma $ map pp (pFinal p)))
           $+$
           (text "PC:" <+> (pp $ pPCEnum p))
           $+$
           (text "Pause conditions:" <+> (hsep $ punctuate comma $ map (\(l,c) -> parens $ pp l <> comma <> pp c) (pPauses p))))

instance Show ProcTrans where
    show = render . pp

-- PID to process name
pidToName :: PID -> String
pidToName pid = intercalate "/" pid

childPID :: PID -> Ident -> PID
childPID pid pname = pid ++ [sname pname]

pidIdle = ["$pididle"]
pidCont = ["$pidcont"]

----------------------------------------------------------------------
-- Names
----------------------------------------------------------------------

--initid = [":init"]


mkVarName :: (WithName a) => Maybe PID -> Maybe Method -> a -> String
mkVarName mpid mmeth x = mkVarNameS mpid mmeth (sname x)

mkVarNameS :: Maybe PID -> Maybe Method -> String -> String
mkVarNameS mpid mmeth s = intercalate "/" names
    where names = fromMaybe [] mpid ++ 
                  fromMaybe [] (fmap ((:[]). (++ "()") . sname) mmeth) ++ 
                  [s]

mkVar :: (WithName a) => Maybe PID -> Maybe Method -> a -> I.Expr
mkVar mpid mmeth x = I.EVar $ mkVarName mpid mmeth x

mkVarS :: Maybe PID -> Maybe Method -> String -> I.Expr
mkVarS mpid mmeth s = I.EVar $ mkVarNameS mpid mmeth s

mkVarDecl :: (?spec::Spec, WithName a, WithType a) => Bool -> Maybe PID -> Maybe Method -> a -> I.Var
mkVarDecl mem mpid mmeth x = I.Var mem I.VarState (mkVarName mpid mmeth x) (mkType $ typ x)

-- Variable that stores return value of a task
mkRetVar :: Maybe PID -> Method -> Maybe I.Expr
mkRetVar mpid meth = case methRettyp meth of
                          Nothing -> Nothing
                          Just _  -> Just $ mkVarS mpid (Just meth) "$ret"

mkRetVarDecl :: (?spec::Spec) => Maybe PID -> Method -> Maybe I.Var
mkRetVarDecl mpid meth = case methRettyp meth of
                              Nothing -> Nothing
                              Just t  -> Just $ I.Var False
                                                      I.VarState
                                                      (mkVarNameS mpid (Just meth) "$ret") 
                                                      (mkType $ Type (ScopeTemplate tmMain) t)

mkEnVarName :: PID -> Maybe Method -> String
mkEnVarName pid mmeth = mkVarNameS (Just pid) mmeth "$en"

mkEnVar :: PID -> Maybe Method -> I.Expr
mkEnVar pid mmeth = I.EVar $ mkEnVarName pid mmeth

mkEnVarDecl :: PID -> Maybe Method -> I.Var
mkEnVarDecl pid mmeth = I.Var False I.VarState (mkEnVarName pid mmeth) I.Bool

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

-- PID of the last process to make a transition
mkPIDVarName :: String
mkPIDVarName = "$pid"

mkPIDVar :: I.Expr
mkPIDVar = I.EVar mkPIDVarName

mkPIDEnumeratorName :: PID -> String
mkPIDEnumeratorName pid = "$" ++ pidToName pid

mkPIDEnum :: PID -> I.Expr
mkPIDEnum = I.EConst . I.EnumVal . mkPIDEnumeratorName

mkPIDVarDecl :: [PID] -> (I.Var, I.Enumeration)
mkPIDVarDecl pids = (I.Var False I.VarState mkPIDVarName (I.Enum "$pidenum"), enum)
    where enum = I.Enumeration "$pidenum" $ map mkPIDEnumeratorName $ pidIdle:pidCont:pids

mkTagVarName :: String
mkTagVarName = "$tag"

mkTagVar :: I.Expr
mkTagVar = I.EVar mkTagVarName

mkTagVarDecl :: (?spec::Spec) => (I.Var, I.Enumeration)
mkTagVarDecl = (I.Var False I.VarState mkTagVarName (I.Enum "$tags"), I.Enumeration "$tags" tags)
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
mkContVarDecl = I.Var False I.VarState mkContVarName I.Bool

mkMagicVarName :: String
mkMagicVarName = "$magic"

mkMagicVar :: I.Expr
mkMagicVar = I.EVar mkMagicVarName

mkMagicVarDecl :: I.Var
mkMagicVarDecl = I.Var False I.VarState mkMagicVarName I.Bool

mkNullVarName :: String
mkNullVarName = "$null"

mkNullVar :: I.Expr
mkNullVar = I.EVar mkNullVarName

mkNullVarDecl :: I.Var
mkNullVarDecl = I.Var False I.VarState mkNullVarName (I.Ptr I.Bool)

mkErrVarName :: String
mkErrVarName = I.cfaErrVarName

mkErrVar :: I.Expr
mkErrVar = I.EVar mkErrVarName

mkErrVarDecl :: I.Var
mkErrVarDecl = I.Var False I.VarState mkErrVarName I.Bool


type NameMap = M.Map Ident I.Expr

methodLMap :: PID -> Method -> NameMap 
methodLMap pid meth = 
    M.fromList $ map (\v -> (name v, mkVar (Just pid) (Just meth) v)) (methVar meth) ++
                 map (\a -> (name a, mkVar (Just pid) (Just meth) a)) (methArg meth)

procLMap :: PID -> Process -> NameMap
procLMap pid p = M.fromList $ map (\v -> (name v, mkVar (Just pid) Nothing v)) (procVar p)

globalNMap :: (?spec::Spec) => NameMap
globalNMap = M.fromList $ gvars ++ wires ++ enums
    where -- global variables
          gvars  = map (\v -> (name v, mkVar Nothing Nothing v)) $ tmVar tmMain
          -- wires
          wires  = map (\w -> (name w, mkVar Nothing Nothing w)) $ tmWire tmMain
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
         Type s (BoolSpec   _)     -> I.Bool
         Type s (SIntSpec   _ w)   -> I.SInt w
         Type s (UIntSpec   _ w)   -> I.UInt w
         Type s (StructSpec _ fs)  -> I.Struct $ map (\(Field _ t n) -> I.Field (sname n) (mkType (Type s t))) fs 
         Type s (EnumSpec   _ es)  -> I.Enum $ getEnumName $ name $ head es
         Type s (PtrSpec    _ t)   -> I.Ptr $ mkType $ Type s t
         Type s (ArraySpec  _ t l) -> let ?scope = s in I.Array (mkType $ Type s t) (fromInteger $ evalInt l)
         Type s t -> error $ "mkType: " ++ show t


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

data CFACtx = CFACtx { ctxPID     :: PID           -- PID of the process being constructed
                     , ctxScope   :: Scope         -- current syntactic scope
                     , ctxCFA     :: I.CFA         -- CFA constructed so far
                     , ctxRetLoc  :: I.Loc         -- return location
                     , ctxBrkLoc  :: I.Loc         -- break location
                     , ctxLHS     :: Maybe I.Expr  -- LHS expression
                     , ctxGNMap   :: NameMap       -- global variable visible in current scope
                     , ctxLNMap   :: NameMap       -- local variable map
                     , ctxLastVar :: Int           -- counter used to generate unique variable names
                     , ctxVar     :: [I.Var]       -- temporary vars
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

ctxInsTransMany :: I.Loc -> I.Loc -> [I.Statement] -> State CFACtx ()
ctxInsTransMany from to stats = modify $ (\ctx -> ctx {ctxCFA = I.cfaInsTransMany from to stats $ ctxCFA ctx})

ctxInsTrans' :: I.Loc -> I.Statement -> State CFACtx I.Loc
ctxInsTrans' from stat = do
    to <- ctxInsLoc
    ctxInsTrans from to stat
    return to

ctxInsTransMany' :: I.Loc -> [I.Statement] -> State CFACtx I.Loc
ctxInsTransMany' from stats = do
    to <- ctxInsLoc
    ctxInsTransMany from to stats
    return to

ctxInsTmpVar :: I.Type -> State CFACtx I.Var
ctxInsTmpVar t = do
    last  <- gets ctxLastVar
    pid   <- gets ctxPID
    scope <- gets ctxScope
    let m = case scope of
                 ScopeMethod _ meth -> Just meth
                 _                  -> Nothing
        name = mkVarNameS (Just pid) m ("$tmp" ++ show (last + 1))
        v = I.Var False I.VarTmp name t
    modify $ (\ctx -> ctx { ctxLastVar = last + 1
                          , ctxVar     = v:(ctxVar ctx)})
    return v

ctxPause :: I.Loc -> I.Expr -> State CFACtx I.Loc
ctxPause loc cond = do after <- ctxInsLocLab (I.LPause cond)
                       ctxInsTrans loc after I.nop
                       case cond of
                            (I.EConst (I.BoolVal True)) -> return after
                            _                           -> ctxInsTrans' after (I.SAssume cond)

ctxFinal :: I.Loc -> State CFACtx I.Loc
ctxFinal loc = do after <- ctxInsLocLab I.LFinal
                  ctxInsTrans loc after I.nop
                  return after

ctxErrTrans :: I.Loc -> I.Statement -> State CFACtx ()
ctxErrTrans loc stat = modify $ (\ctx -> ctx {ctxCFA = I.cfaErrTrans loc stat $ ctxCFA ctx})

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
