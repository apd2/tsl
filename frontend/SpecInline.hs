{-# LANGUAGE ImplicitParams #-}

-- Convert flattened spec to internal representation
module SpecInline () where

import Data.List
import Data.Maybe

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
-- * Function calls can only appear in top-level expressions
-- * No function calls in return statements
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

-- Process ID (path in the process tree)
type PID = [String]

initid = [":init"]


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
