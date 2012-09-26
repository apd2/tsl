{-# LANGUAGE ImplicitParams #-}

module ExprInline(tmpName,
                  exprSimplify,
                  exprSimplifyAsn,
                  exprToIExpr) where

import Data.List
import Data.Maybe
import Control.Monad.State
import qualified Data.Map as M

import qualified ISpec as I
import TSLUtil
import NS
import Pos
import Name
import Spec
import Expr
import ExprOps
import Statement
import Var
import Type
import TypeOps
import Inline

tmpName :: Pos -> Uniq -> Ident
tmpName p u = Ident p $ "$" ++ (show $ getUniq u)

-- Extract all function calls from expression to a list of temporary
-- assignment statements
exprSimplify :: (?spec::Spec, ?scope::Scope, ?uniq::Uniq) => Expr -> ([Statement], Expr)
exprSimplify e@(EApply p mref as)  = (ss, e')
    where (argss, as') = unzip $ map exprSimplify as
          tmp = tmpName p ?uniq
          decl = SVarDecl p (Var p (tspec e) tmp Nothing)
          asn = SAssign p (ETerm p [tmp]) (EApply p mref as')
          ss = (concat argss) ++ [decl,asn]
          e' = ETerm p [tmp]
exprSimplify (EField p s f)           = let (ss,s') = exprSimplify s
                                        in (ss, EField p s' f)
exprSimplify (EPField p s f)          = let (ss,s') = exprSimplify s
                                        in (ss, EPField p s' f)
exprSimplify (EIndex p a i)           = let (ssa,a') = exprSimplify a
                                            (ssi,i') = exprSimplify i
                                        in (ssa++ssi, EIndex p a' i')
exprSimplify (EUnOp p op a)           = let (ss,a') = exprSimplify a
                                        in (ss, EUnOp p op a')
exprSimplify (EBinOp p op a1 a2)      = let (ss1,a1') = exprSimplify a1
                                            (ss2,a2') = exprSimplify a2
                                        in ((ss1++ss2), EBinOp p op a1' a2')
exprSimplify e@(ETernOp p a1 a2 a3)   = condSimplify p (Left $ tspec e) [(a1,a2)] (Just a3)
exprSimplify e@(ECase p c cs md)      = condSimplify p (Left $ tspec e) cs' md
                                        where cs' = map (mapFst $ (\e -> EBinOp (pos e) Eq c e)) cs
exprSimplify e@(ECond p cs md)        = condSimplify p (Left $ tspec e) cs md
exprSimplify (ESlice p e (l,h))       = let (ss, e') = exprSimplify e
                                            (ssl,l') = exprSimplify l
                                            (ssh,h') = exprSimplify h
                                        in (ss++ssl++ssh, ESlice p e' (l',h'))
exprSimplify (EStruct p n (Left fs))  = let (ss,fs') = unzip $ map exprSimplify (snd $ unzip fs)
                                        in (concat ss, EStruct p n (Left $ zip (fst $ unzip fs) fs'))
exprSimplify (EStruct p n (Right fs)) = let (ss,fs') = unzip $ map exprSimplify fs
                                        in (concat ss, EStruct p n (Right fs'))
exprSimplify e                        = ([], e)


-- Like exprSimplify, but don't expand the top-level method call or conditional expression
-- and assign it directly to lhs, which is assumed to be already simplified.
exprSimplifyAsn :: (?spec::Spec, ?scope::Scope, ?uniq::Uniq) => Pos -> Expr -> Expr -> [Statement]
exprSimplifyAsn p lhs (EApply p' mref as)  = (concat argss) ++ [asn]
    where (argss, as') = unzip $ map exprSimplify as
          asn = SAssign p lhs (EApply p' mref as')
exprSimplifyAsn p lhs (ETernOp _ a1 a2 a3) = fst $ condSimplify p (Right lhs) [(a1,a2)] (Just a3)
exprSimplifyAsn p lhs (ECase _ c cs md)    = fst $ condSimplify p (Right lhs) cs' md
                                             where cs' = map (mapFst $ (\e -> EBinOp (pos e) Eq c e)) cs
exprSimplifyAsn p lhs (ECond _ cs md)      = fst $ condSimplify p (Right lhs) cs md
exprSimplifyAsn p lhs rhs                  = let (ss, rhs') = exprSimplify rhs
                                             in ss++[SAssign p lhs rhs']


condSimplify :: (?spec::Spec, ?scope::Scope, ?uniq::Uniq) => Pos -> Either TypeSpec Expr -> [(Expr, Expr)] -> Maybe Expr -> ([Statement], Expr)
condSimplify p mlhs cs mdef = 
    let (sdecl, lhs) = case mlhs of
                            Left t  -> let tmp = tmpName p ?uniq
                                       in ([SVarDecl p $ Var p t tmp Nothing], ETerm p [tmp])
                            Right e -> ([],e)
        (ss,conds) = unzip $ map exprSimplify (fst $ unzip cs)
        negations = map (\es -> map (\e -> EUnOp (pos e) Not e) es) (inits conds)
        conds' = (map (\(c,n) -> eAnd (pos c) (c:n)) (zip conds negations)) ++ [eAnd nopos $ last negations]
        assumes = map (SAssume p) conds'
        stats = map (\me -> case me of
                                 Just e -> let (ss, e') = exprSimplify e
                                               asn = SAssign (pos e) lhs e'
                                               in ss ++ [asn]
                                 Nothing -> [SAssert p (EBool p False)])
                    ((map Just $ snd $ unzip cs) ++ [mdef])
        choices = map (\(a,s) -> sSeq (pos a) (a:s)) (zip assumes stats)
    in (sdecl ++ (concat ss) ++ [SChoice p choices], lhs)


----------------------------------------------------------------------
-- Convert expressions to internal format
----------------------------------------------------------------------

exprToIExpr :: (?spec::Spec) => Expr -> State CFACtx I.Expr
exprToIExpr (ETerm _ ssym) = do
    scope <- gets ctxScope
    lmap  <- gets ctxLNMap
    gmap  <- gets ctxGNMap
    let n = case getTerm scope ssym of
                 ObjVar      _ v -> name v
                 ObjGVar     _ v -> name v
                 ObjWire     _ w -> name w
                 ObjArg      _ a -> name a
                 ObjConst    _ c -> name c
                 ObjEnum     _ e -> name e
    return $ case M.lookup n gmap of
                  Just e -> e
                  Nothing -> case M.lookup n lmap of
                                  Just e  -> e
                                  Nothing -> error $ "exprToIExpr: unknown name: " ++ sname n

exprToIExpr (ELit _ _ _ _ v)             = return $ I.EConst $ I.IntVal v
exprToIExpr (EBool _ b)                  = return $ I.EConst $ I.BoolVal b
exprToIExpr (EField _ e f)               = do e' <- exprToIExpr e
                                              return $ I.EField e' (sname f)
exprToIExpr (EPField _ e f)              = do e' <- exprToIExpr e
                                              let e'' = I.EUnOp Deref e'
                                              return $ I.EField e'' (sname f)
exprToIExpr (EIndex _ e i)               = do e' <- exprToIExpr e
                                              i' <- exprToIExpr i
                                              return $ I.EIndex e' i'
exprToIExpr (EUnOp _ op e)               = do e' <- exprToIExpr e
                                              return $ I.EUnOp op e'
exprToIExpr (EBinOp _ op e1 e2)          = do e1' <- exprToIExpr e1
                                              e2' <- exprToIExpr e2
                                              return $ I.EBinOp op e1' e2'
exprToIExpr (ESlice _ e (l,h))           = do scope <- gets ctxScope
                                              let ?scope = scope
                                              e' <- exprToIExpr e
                                              let l' = fromInteger $ evalInt l
                                                  h' = fromInteger $ evalInt h
                                              return $ I.ESlice e' (l',h')
exprToIExpr e@(EStruct _ tname (Left fs))= do scope <- gets ctxScope
                                              let ?scope = scope
                                              let StructSpec _ sfs = tspec $ typ' e
                                              fs' <- mapM (exprToIExpr . snd . fromJust . (\f -> find ((==f) . fst) fs) . name) sfs
                                              return $ I.EStruct (sname $ head tname) fs'
exprToIExpr (EStruct _ tname (Right fs)) = do fs' <- mapM exprToIExpr fs
                                              return $ I.EStruct (sname $ head tname) fs'
exprToIExpr (ENonDet _)                  = return I.ENonDet
