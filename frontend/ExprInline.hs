{-# LANGUAGE ImplicitParams #-}

module ExprInline(NameGen,
                  exprSimplify,
                  exprSimplifyAsn,
                  exprToIExprDet,
                  exprToIExpr,
                  exprToIExprs) where

import Data.List
import Data.Maybe
import Control.Monad.State
import qualified Data.Map as M

import qualified IExpr as I
import qualified IType as I
import qualified IVar  as I
import qualified CFA   as I
import qualified ISpec as I
import Util hiding (name, trace)
import NS
import Pos
import Name
import Spec
import Expr
import ExprOps
import Statement
import TVar
import Type
import TypeOps
import Inline
import Const

type NameGen a = State (Int, [Var]) a

tmpVar :: Pos -> Bool -> TypeSpec -> NameGen Var
tmpVar p mem t = do
    (lst,vars) <- get
    let nam = Ident p $ "$" ++ show lst
        var = Var p mem t nam Nothing
    put (lst + 1, vars++[var])
    return var

-- Extract all function calls from expression to a list of temporary
-- assignment statements
exprSimplify :: (?spec::Spec, ?scope::Scope) => Expr -> NameGen ([Statement], Expr)
exprSimplify e = liftM (mapSnd exprFlattenStruct) $ exprSimplify' e

exprSimplify' :: (?spec::Spec, ?scope::Scope) => Expr -> NameGen ([Statement], Expr)
exprSimplify' e@(EApply p mref mas)     = do 
    (argss, mas') <- liftM unzip $ mapM (maybe (return ([], Nothing)) (liftM (mapSnd Just) . exprSimplify)) mas
    var <- tmpVar p False (tspec e)
    let decl = SVarDecl p Nothing var
        asn = SAssign p Nothing (ETerm p [name var]) (EApply p mref mas')
        ss = (concat argss) ++ [decl,asn]
        e' = ETerm p [name var]
    return (ss, e')
exprSimplify' (EField p s f)            = do (ss,s') <- exprSimplify s
                                             return (ss, EField p s' f)
exprSimplify' (EPField p s f)           = do (ss,s') <- exprSimplify s
                                             return (ss, EPField p s' f)
exprSimplify' (EIndex p a i)            = do (ssa,a') <- exprSimplify a
                                             (ssi,i') <- exprSimplify i
                                             return (ssa++ssi, EIndex p a' i')
exprSimplify' (EUnOp p op a)            = do (ss,a') <- exprSimplify a
                                             return (ss, EUnOp p op a')
exprSimplify' (EBinOp p op a1 a2)       = do (ss1,a1') <- exprSimplify a1
                                             (ss2,a2') <- exprSimplify a2
                                             return ((ss1++ss2), EBinOp p op a1' a2')
exprSimplify' e@(ETernOp p a1 a2 a3)    = condSimplify p (Left $ tspec e) [(a1,a2)] (Just a3)
exprSimplify' e@(ECase p c cs md)       = do (ss, c') <- exprSimplify c
                                             let cs' = map (mapFst $ (\e' -> EBinOp (pos e') Eq c' e')) cs
                                             liftM (mapFst (ss++)) $ condSimplify p (Left $ tspec e) cs' md
exprSimplify' e@(ECond p cs md)         = condSimplify p (Left $ tspec e) cs md
exprSimplify' (ESlice p e (l,h))        = do (ss, e') <- exprSimplify e
                                             (ssl,l') <- exprSimplify l
                                             (ssh,h') <- exprSimplify h
                                             return (ss++ssl++ssh, ESlice p e' (l',h'))
exprSimplify' (EStruct p n (Left fs))   = do (ss,fs') <- liftM unzip $ mapM exprSimplify (snd $ unzip fs)
                                             return (concat ss, EStruct p n (Left $ zip (fst $ unzip fs) fs'))
exprSimplify' (EStruct p n (Right fs))  = do (ss,fs') <- liftM unzip $ mapM exprSimplify fs
                                             return (concat ss, EStruct p n (Right fs'))
exprSimplify' e@(ETerm _ t)             = case getTerm ?scope t of
                                               ObjConst _ c -> return ([],constVal c)
                                               _            -> return ([],e)
exprSimplify' (ERel p n as)             = do 
    (argss, as') <- liftM unzip $ mapM exprSimplify as
    return (concat argss, ERel p n as')
exprSimplify' e                         = return ([], e)


-- Like exprSimplify, but don't expand the top-level method call or conditional expression
-- and assign it directly to lhs, which is assumed to be already simplified.
exprSimplifyAsn :: (?spec::Spec, ?scope::Scope) => Pos -> Expr -> Expr -> NameGen [Statement]
exprSimplifyAsn p lhs (EApply p' mref mas)  = do
    (argss, mas') <- liftM unzip $ mapM (maybe (return ([], Nothing)) ((liftM $ mapSnd Just) . exprSimplify)) mas
    let asn = SAssign p Nothing lhs (EApply p' mref mas')
    return $ (concat argss) ++ [asn]
exprSimplifyAsn p lhs (ETernOp _ a1 a2 a3) = liftM fst $ condSimplify p (Right lhs) [(a1,a2)] (Just a3)
exprSimplifyAsn p lhs (ECase _ c cs md)    = do let cs' = map (mapFst $ (\e -> EBinOp (pos e) Eq c e)) cs
                                                liftM fst $ condSimplify p (Right lhs) cs' md
exprSimplifyAsn p lhs (ECond _ cs md)      = liftM fst $ condSimplify p (Right lhs) cs md
exprSimplifyAsn p lhs rhs                  = do (ss, rhs') <- exprSimplify rhs
                                                return $ ss++[SAssign p Nothing lhs rhs']

condSimplify :: (?spec::Spec, ?scope::Scope) => Pos -> Either TypeSpec Expr -> [(Expr, Expr)] -> Maybe Expr -> NameGen ([Statement], Expr)
condSimplify p mlhs cs mdef = do
    (sdecl, lhs) <- case mlhs of
                         Left t  -> do var <- tmpVar p False t
                                       return ([SVarDecl p Nothing var], ETerm p [name var])
                         Right e -> return ([],e)
    (ss,conds) <- liftM unzip $ mapM exprSimplify (fst $ unzip cs)
    stats <- mapM (\me -> case me of
                               Just e  -> do (ss', e') <- exprSimplify e
                                             let asn = SAssign (pos e) Nothing lhs e'
                                             return $ sSeq (pos e) Nothing (ss' ++ [asn])
                               Nothing -> return (SAssert p Nothing (EBool p False)))
                  ((map Just $ snd $ unzip cs) ++ [mdef])
    return (sdecl ++ (concat ss) ++ [mkif (zip conds stats) (last stats)], lhs)

mkif :: [(Expr, Statement)] -> Statement -> Statement
mkif []          def = def
mkif ((c,s):ifs) def = SITE (pos c) Nothing c s $ Just $ mkif ifs def

-- Eliminate constructs of the form:
-- struct_name{f1=...,f2=...}.f1 in a simplified expression
exprFlattenStruct :: (?spec::Spec, ?scope::Scope) => Expr -> Expr
exprFlattenStruct = mapExpr exprFlattenStruct' ?scope 

exprFlattenStruct' :: (?spec::Spec) => Scope -> Expr -> Expr
exprFlattenStruct' _ (EField _ (EStruct _ _ (Left fs)) f)    = snd $ fromJust $ find ((==f) . fst) fs
exprFlattenStruct' s (EField _ e@(EStruct _ _ (Right fs)) f) = fs !! idx
    where StructSpec _ fs' = let ?scope = s in tspec $ typ' e
          idx = fromJust $ findIndex ((==f) . name) fs' 
exprFlattenStruct' _ e                                       = e

----------------------------------------------------------------------
-- Convert (simplified) expressions to internal format
----------------------------------------------------------------------

exprToIExprDet :: (?spec::Spec, ?ispec::I.Spec) => Expr -> State CFACtx I.Expr
exprToIExprDet e = exprToIExpr e $ error "exprToIExprDet applied to non-deterministic expression"

exprToIExpr :: (?spec::Spec, ?ispec::I.Spec) => Expr -> TypeSpec -> State CFACtx I.Expr
exprToIExpr e t = do sc <- gets ctxScope
                     exprToIExpr' e (typ' $ Type sc t)

-- Like exprToIExpr, but expand top-level EStruct into a list of fields
exprToIExprs :: (?spec::Spec, ?ispec::I.Spec) => Expr -> TypeSpec -> State CFACtx [(I.Expr,I.Type)]
exprToIExprs e@(EStruct _ _ (Left fs)) _ = do 
    sc <- gets ctxScope
    let ?scope = sc
    let Type _ (StructSpec _ sfs) = typ' e
    fs' <- mapM (\f -> do let v = snd $ fromJust $ (\n -> find ((==n) . fst) fs) $ name f
                          exprToIExprs v (tspec f)) sfs
    return $ concat fs'
exprToIExprs e@(EStruct _ _ (Right fs)) _ = do 
    sc <- gets ctxScope
    let ?scope = sc
    let Type _ (StructSpec _ sfs) = typ' e
    fs' <- mapM (\(f,v) -> exprToIExprs v (tspec f)) $ zip sfs fs
    return $ concat fs'
exprToIExprs e t                              = do 
    sc <- gets ctxScope
    let ?scope = sc
    e' <- exprToIExpr e t
    let t' = case e of
                  ENonDet _ -> mkType $ Type sc t
                  _         -> mkType $ typ e
    return [(e', t')]

exprToIExpr' :: (?spec::Spec, ?ispec::I.Spec) => Expr -> Type -> State CFACtx I.Expr
exprToIExpr' (ETerm _ ssym) _ = do
    sc    <- gets ctxScope
    lmap  <- gets ctxLNMap
    gmap  <- gets ctxGNMap
    let n = case getTerm sc ssym of
                 ObjVar      _ v -> name v
                 ObjGVar     _ v -> name v
                 ObjWire     _ w -> name w
                 ObjArg      _ a -> name a
                 ObjEnum     _ e -> name e
                 ObjConst    _ c -> name c
    return $ case M.lookup n gmap of
                  Just e -> e
                  Nothing -> case M.lookup n lmap of
                                  Just e  -> e
                                  Nothing -> error $ "exprToIExpr: unknown name: " ++ sname n

exprToIExpr' (ELit _ w True _ v) _          = return $ I.EConst $ I.SIntVal w v
exprToIExpr' (ELit _ w False _ v) _         = return $ I.EConst $ I.UIntVal w v
exprToIExpr' (EBool _ b) _                  = return $ I.EConst $ I.BoolVal b
exprToIExpr' (EField _ e f) _               = do e' <- exprToIExprDet e
                                                 return $ I.EField e' (sname f)
exprToIExpr' (EPField _ e f) _              = do e' <- exprToIExprDet e
                                                 let e'' = I.EUnOp Deref e'
                                                 return $ I.EField e'' (sname f)
exprToIExpr' (EIndex _ e i) _               = do e' <- exprToIExprDet e
                                                 i' <- exprToIExprDet i
                                                 return $ I.EIndex e' i'
exprToIExpr' (EUnOp _ op e) _               = do e' <- exprToIExprDet e
                                                 return $ I.EUnOp op e'
exprToIExpr' (EBinOp _ Eq e1 e2) _          = do sc <- gets ctxScope
                                                 let ?scope = sc
                                                 e1' <- mapM exprToIExprDet $ exprScalars e1
                                                 e2' <- mapM exprToIExprDet $ exprScalars e2
                                                 return $ I.conj $ zipWith (I.EBinOp Eq) e1' e2'
exprToIExpr' (EBinOp _ Neq e1 e2) _         = do sc <- gets ctxScope
                                                 let ?scope = sc
                                                 e1' <- mapM exprToIExprDet $ exprScalars e1
                                                 e2' <- mapM exprToIExprDet $ exprScalars e2
                                                 return $ I.disj $ zipWith (I.EBinOp Neq) e1' e2'
exprToIExpr' (EBinOp _ op e1 e2) _          = do e1' <- exprToIExprDet e1
                                                 e2' <- exprToIExprDet e2
                                                 return $ I.EBinOp op e1' e2'
exprToIExpr' (ESlice _ e (l,h)) _           = do sc <- gets ctxScope
                                                 let ?scope = sc
                                                 e' <- exprToIExprDet e
                                                 let l' = fromInteger $ evalInt l
                                                     h' = fromInteger $ evalInt h
                                                 return $ I.ESlice e' (l',h')
exprToIExpr' (EAtLab _ lab) _               = return
                                              $ I.disj 
                                              $ map (\(pid, p) -> I.disj 
                                                                  $ map (\loc -> mkPCEq (I.procCFA p) pid (mkPC pid loc)) 
                                                                                 $ I.cfaFindLabel (I.procCFA p) (sname lab)) 
                                              $ I.specAllProcs ?ispec
exprToIExpr' (ERel _ n as) _                = do as' <- mapM exprToIExprDet as
                                                 return $ I.ERel (sname n) as'
exprToIExpr' (ENonDet _) t                  = do v <- ctxInsTmpVar $ mkType t
                                                 return $ I.EVar $ I.varName v
exprToIExpr' e _                            = error $ "exprToIExpr' " ++ show e
