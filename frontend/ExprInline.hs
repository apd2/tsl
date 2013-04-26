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
import TSLUtil
import Util hiding (name)
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
    (last,vars) <- get
    let nam = Ident p $ "$" ++ show last
        var = Var p mem t nam Nothing
    put (last + 1, vars++[var])
    return var

-- Extract all function calls from expression to a list of temporary
-- assignment statements
exprSimplify :: (?spec::Spec, ?scope::Scope) => Expr -> NameGen ([Statement], Expr)
exprSimplify e = liftM (mapSnd exprFlattenStruct) $ exprSimplify' e

exprSimplify' :: (?spec::Spec, ?scope::Scope) => Expr -> NameGen ([Statement], Expr)
exprSimplify' e@(EApply p mref as)      = do 
    (argss, as') <- liftM unzip $ mapM exprSimplify as
    var <- tmpVar p False (tspec e)
    let decl = SVarDecl p var
        asn = SAssign p (ETerm p [name var]) (EApply p mref as')
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
                                             let cs' = map (mapFst $ (\e -> EBinOp (pos e) Eq c' e)) cs
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
exprSimplify' e@(ETerm p t)             = case getTerm ?scope t of
                                               ObjConst _ c -> return ([],constVal c)
                                               _            -> return ([],e)
exprSimplify' e                         = return ([], e)


-- Like exprSimplify, but don't expand the top-level method call or conditional expression
-- and assign it directly to lhs, which is assumed to be already simplified.
exprSimplifyAsn :: (?spec::Spec, ?scope::Scope) => Pos -> Expr -> Expr -> NameGen [Statement]
exprSimplifyAsn p lhs (EApply p' mref as)  = do
    (argss, as') <- liftM unzip $ mapM exprSimplify as
    let asn = SAssign p lhs (EApply p' mref as')
    return $ (concat argss) ++ [asn]
exprSimplifyAsn p lhs (ETernOp _ a1 a2 a3) = liftM fst $ condSimplify p (Right lhs) [(a1,a2)] (Just a3)
exprSimplifyAsn p lhs (ECase _ c cs md)    = do let cs' = map (mapFst $ (\e -> EBinOp (pos e) Eq c e)) cs
                                                liftM fst $ condSimplify p (Right lhs) cs' md
exprSimplifyAsn p lhs (ECond _ cs md)      = liftM fst $ condSimplify p (Right lhs) cs md
exprSimplifyAsn p lhs rhs                  = do (ss, rhs') <- exprSimplify rhs
                                                return $ ss++[SAssign p lhs rhs']

condSimplify :: (?spec::Spec, ?scope::Scope) => Pos -> Either TypeSpec Expr -> [(Expr, Expr)] -> Maybe Expr -> NameGen ([Statement], Expr)
condSimplify p mlhs cs mdef = do
    (sdecl, lhs) <- case mlhs of
                         Left t  -> do var <- tmpVar p False t
                                       return ([SVarDecl p var], ETerm p [name var])
                         Right e -> return ([],e)
    (ss,conds) <- liftM unzip $ mapM exprSimplify (fst $ unzip cs)
    let negations = map (\es -> map (\e -> EUnOp (pos e) Not e) es) (inits conds)
        conds' = (map (\(c,n) -> eAnd (pos c) (c:n)) (zip conds negations)) ++ [eAnd nopos $ last negations]
        assumes = map (SAssume p) conds'
    stats <- mapM (\me -> case me of
                               Just e  -> do (ss, e') <- exprSimplify e
                                             let asn = SAssign (pos e) lhs e'
                                             return $ ss ++ [asn]
                               Nothing -> return[SAssert p (EBool p False)])
                  ((map Just $ snd $ unzip cs) ++ [mdef])
    let choices = map (\(a,s) -> sSeq (pos a) (a:s)) (zip assumes stats)
    return (sdecl ++ (concat ss) ++ [SChoice p choices], lhs)


-- Eliminate constructs of the form:
-- struct_name{f1=...,f2=...}.f1 in a simplified expression
exprFlattenStruct :: (?spec::Spec, ?scope::Scope) => Expr -> Expr
exprFlattenStruct = mapExpr exprFlattenStruct' ?scope 

exprFlattenStruct' :: (?spec::Spec) => Scope -> Expr -> Expr
exprFlattenStruct' _ (EField _ (EStruct _ n (Left fs)) f)    = snd $ fromJust $ find ((==f) . fst) fs
exprFlattenStruct' s (EField _ e@(EStruct _ n (Right fs)) f) = fs !! idx
    where StructSpec _ fs' = let ?scope = s in tspec $ typ' e
          idx = fromJust $ findIndex ((==f) . name) fs' 
exprFlattenStruct' _ e                                       = e

----------------------------------------------------------------------
-- Convert (simplified) expressions to internal format
----------------------------------------------------------------------

exprToIExprDet :: (?spec::Spec) => Expr -> State CFACtx I.Expr
exprToIExprDet e = exprToIExpr e $ error "exprToIExprDet applied to non-deterministic expression"

exprToIExpr :: (?spec::Spec) => Expr -> TypeSpec -> State CFACtx I.Expr
exprToIExpr e t = do scope <- gets ctxScope
                     exprToIExpr' e (typ' $ Type scope t)

-- Like exprToIExpr, but expand top-level EStruct into a list of fields
exprToIExprs :: (?spec::Spec) => Expr -> TypeSpec -> State CFACtx [(I.Expr,I.Type)]
exprToIExprs e@(EStruct _ tname (Left fs)) _ = do 
    scope <- gets ctxScope
    let ?scope = scope
    let Type sscope (StructSpec _ sfs) = typ' e
    fs' <- mapM (\f -> do let v = snd $ fromJust $ (\f -> find ((==f) . fst) fs) $ name f
                          exprToIExprs v (tspec f)) sfs
    return $ concat fs'
exprToIExprs e@(EStruct _ tname (Right fs)) _ = do 
    scope <- gets ctxScope
    let ?scope = scope
    let Type sscope (StructSpec _ sfs) = typ' e
    fs' <- mapM (\(f,v) -> exprToIExprs v (tspec f)) $ zip sfs fs
    return $ concat fs'
exprToIExprs e t                              = do 
    scope <- gets ctxScope
    let ?scope = scope
    e' <- exprToIExpr e t
    let t' = case e of
                  ENonDet _ -> mkType $ Type scope t
                  _         -> mkType $ typ e
    return [(e', t')]

exprToIExpr' :: (?spec::Spec) => Expr -> Type -> State CFACtx I.Expr
exprToIExpr' e@(ETerm _ ssym) _ = do
    scope <- gets ctxScope
    lmap  <- gets ctxLNMap
    gmap  <- gets ctxGNMap
    let n = case getTerm scope ssym of
                 ObjVar      _ v -> name v
                 ObjGVar     _ v -> name v
                 ObjWire     _ w -> name w
                 ObjArg      _ a -> name a
                 ObjEnum     _ e -> name e
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
exprToIExpr' (EBinOp _ op e1 e2) _          = do e1' <- exprToIExprDet e1
                                                 e2' <- exprToIExprDet e2
                                                 return $ I.EBinOp op e1' e2'
exprToIExpr' (ESlice _ e (l,h)) _           = do scope <- gets ctxScope
                                                 let ?scope = scope
                                                 e' <- exprToIExprDet e
                                                 let l' = fromInteger $ evalInt l
                                                     h' = fromInteger $ evalInt h
                                                 return $ I.ESlice e' (l',h')
exprToIExpr' (ENonDet _) t                  = do v <- ctxInsTmpVar $ mkType t
                                                 return $ I.EVar $ I.varName v
