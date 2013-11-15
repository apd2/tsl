{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module AbsRelation (instantiateRelation) where

import IRelation
import Predicate
import IExpr
import ISpec
import CFA2ACFA
import ACFA2HAST
import MkPredicate
import CFA

type RelInst f e c = (Predicate, [TAST f e c])

-- Assumes that all dereference operations have already been expanded
instantiateRelation :: (?spec::Spec, ?pred::[Predicate]) => Relation -> [Expr] -> RelInst f e c
instantiateRelation Relation{..} args = (p, asts)
    where
    p@PRel{..} = mkPRel relName args
    substs = zip (map fst relArgs) pArgs
    asts = map (\r -> let cfa' = cfaMapExpr r exprSubst
                      in compileACFA [] $ tranCFAToACFA [] cfaInitLoc cfa') relRules
    exprSubst :: Expr -> Expr
    exprSubst = mapExpr exprSubst'
    exprSubst' :: Expr -> Expr
    exprSubst' e@(EVar v) = case lookup v substs of
                                 Nothing -> e
                                 Just e' -> e'
    exprSubst' e          = e
