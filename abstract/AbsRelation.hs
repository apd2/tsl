{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module AbsRelation (RelInst,
                    instantiateRelation) where

import Util
import IRelation
import Predicate
import IExpr
import ISpec
import IType
import CFA2ACFA
import ACFA2HAST
import MkPredicate
import CFA

type RelInst = (Predicate, [ACFA])

-- Assumes that all dereference operations have already been expanded
instantiateRelation :: (?spec::Spec, ?pred::[Predicate]) => Relation -> [Expr] -> RelInst
instantiateRelation Relation{..} args = (p, acfas)
    where
    p@PRel{..} = mkPRel relName args
    substs = zip (map fst relArgs) pArgs
    acfas = map (\r -> let cfa' = cfaMapExpr r exprSubst
                       in tranCFAToACFA [] cfaInitLoc cfa') relRules

    exprSubst :: Expr -> Expr
    exprSubst e@(EVar v)          = case lookup v substs of
                                         Nothing -> e
                                         Just e' -> e'
    exprSubst e@(EConst _)        = e
    exprSubst   (EField e f)      = EField (exprSubst e) f
    exprSubst   (EIndex a i)      = case exprSubst a of
                                         ERange a' f _ -> EIndex a' (plusmod a' [f, exprSubst i])
                                         a'            -> EIndex a' (exprSubst i)
    exprSubst   (ERange a f t)    = case exprSubst a of
                                         ERange a' f' t' -> ERange a' (plusmod a' [exprSubst f,f']) (plusmod a' [exprSubst f,t'])
                                         a'              -> ERange a' (exprSubst f) (exprSubst t)
    exprSubst   (EUnOp op e)      = EUnOp op (exprSubst e)
    exprSubst   (EBinOp op e1 e2) = EBinOp op (exprSubst e1) (exprSubst e2)
    exprSubst   (ESlice e s)      = exprSlice (exprSubst e) s
    exprSubst   (ERel n as)       = ERel n $ map exprSubst as
