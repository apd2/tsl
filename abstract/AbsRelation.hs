{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module AbsRelation (RelInst,
                    instantiateRelation) where

import IRelation
import Predicate
import IExpr
import ISpec
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
    acfas = map (\r -> let cfa' = cfaMapExpr r (mapExpr exprSubst)
                       in tranCFAToACFA [] cfaInitLoc cfa') relRules

    exprSubst :: Expr -> Expr
    exprSubst e@(EVar v) = case lookup v substs of
                                Nothing -> e
                                Just e' -> e'
    exprSubst e          = e
