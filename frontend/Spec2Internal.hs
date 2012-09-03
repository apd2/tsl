-- Convert flattened spec to internal representation
module Spec2Internal () where

import Spec
import qualified ISpec as I

-- Preprocess all statements and expressions before inlining.  
-- In the preprocessed spec:
-- * Function calls can only appear in top-level expressions
-- * Local variables are declared and initialised separately
specSimplify :: Spec -> Spec
statSimplify :: Stat -> Stat
exprSimplify :: Expr -> ([Statement], Expr)




spec2Internal :: Spec -> I.Spec
spec2Internal s = I.Spec senum svar sproc sctl sinvis sinit sgoal
    where ?spec = specSimplify s -- preprocessing
          tmmain = head $ specTemplate ?spec
          senum = mapMaybe (\d -> case tspec d of
                                     EnumSpec _ es -> I.Enum (sname d) (map sname es)
                                     _             -> Nothing) (specType ?spec)
          tagvar =
          lvars  = 
          initstat = statSimplify $ -- compute init statement from global variable assignments and init blocks
          (sinit, initvars)  = proc2CFA initid (ScopeTemplate tmmain) initstat


-- Process ID (path in the process tree)
type PID = [String]

initid = [":init"]

procChildren :: Statement -> [(String, Statement)]

-- Inline process and convert it to CFA form
proc2CFA :: (?spec::Spec) => PID -> Scope -> Statement -> (I.CFA, [I.Var])
proc2CFA pid scope st = (stat2CFA st', vars)
    where st'  = procInline pid scope st
          vars = map (\v -> I.Var ((sname v) VarState (tspec2Internal $ tspec v)) (statVar st')


-- Inline all method invocations in a process.  
-- The process must be in the preprocessed format
-- s   - syntactic scope of the statement (template, process, or method)
procInline :: (?spec::Spec) => PID -> Scope -> Statement -> Statement
procInline pid scope st = 
    let ?pid = pid
        ?scope = scope
        ?mlhs = Nothing
        ?retlab = error "no retlab in a process"
        vars = map (SVarDecl nopos) $ statRenameVars s st
        st' = statInline pid scope st
    in sseq (pos st) (vars++st')

--
--
--
statInline :: (?spec::Spec,?pid::PID,?scope::Scope,?mlhs::Maybe Expr,?retlab::SrcLabel) -> Statement -> [Statement]
statInline (SVarDecl _ _)       = []
statInline (SReturn p Nothing)  = [SGoTo p ?retlab]
statInline (SReturn p (Just e)) = case mlhs of
                                       Nothing  -> [exprInline e, SGoTo p ?retlab]
                                       Just lhs -> [SAssign p lhs (exprInline e), SGoTo p ?retlab]
statInline (SSeq p ss)          = [SSeq p (concaMap statInline ss)]
statInline (SPar p ss)          = [SPar p ss]
statInline (SForever p s)       = [SForever p (sstatInline s)]
statInline (SDo p b c)          = [SDo p (sstatInline b) (exprInline c)]
statInline (SWhile p c b)       = [SWhile p (exprInline c) (sstatInline b)]
statInline (SFor p (mi,c,s) b}  = [SFor p (fmap sstatInline mi, exprInline c, sstatInline s) (sstatInline b)]
statInline (SChoice p ss)       = [SChoice p (map sstatInline ss)]
statInline (SInvoke p mref as)  = callInline p mref as Nothing
statInline (SAssert p c)        = [SAssert p (exprInline c)]
statInline (SAssume p c)        = [SAssume p (exprInline c)]

-- TODO : assignment to output argument
statInline (SAssign p l (EApply p' mref as)) = callInline p' mref as (Just $ exprInline l)
statInline (SAssign p l r)      = [SAssign p (exprInline l) (exprInline r)]
statInline (SITE p c t me)      = [SITE p (exprInline c) (statInline t) (fmap statInline me)]
statInline (SCase p c cs md)    = [SCase p (exprInline c) (map (\(c,s) -> (exprInline c, statInline s)) cs) (fmap statInline md)]
statInline (SMagic p (Right e)  = [SMagic p (Right $ exprInline e)]
statInline st                   = st

sstatInline = sseq . statInline

callInline :: (?spec::Spec,?pid::PID,?scope::Scope) -> Pos -> MethodRef -> [Expr] -> Maybe LExpr -> [Statement]
callInline p mref args mlhs = sseq $ pause ++ tag ++ sargs ++ body ++ [SSrcLab p ?retlab]
    where (tm, m) = getMethod ?scope mref
          pause = case methCat m of
                       Task Controllable   -> [SPause p]
                       Task Uncontrollable -> [SPause p]
                       _                   -> []
          tag = if methCat m `elem` [Task Controllable,Tasl Uncontrollable]
                   then [SAssign (pos mref) tagExpr (taskTag m)]
                   else []
          argnames = map (argName m) (methArg m)
          sargs = map (\n a -> SAssign (pos a) (ETerm (pos a) n) (exprInline a)) (zip argnames args)
          (body,lab) = let ?scope  = ScopeMethod tm m
                           ?mlhs   = mlhs
                           ?retlab = labelFromPos p
                       in (statInline $ fromRight $ methBody m, ?retlab)
