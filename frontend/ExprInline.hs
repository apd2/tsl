{-# LANGUAGE ImplicitParams #-}

module ExprInline(tmpName,
                  exprSimplify,
                  exprSimplifyAsn) where

import Data.List

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
