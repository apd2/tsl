{-# LANGUAGE ImplicitParams #-}

module AbsRelation where

import IRelation
import Predicate
import IExpr
import ISpec

type RelInst = (Predicate, [Expr])

instantiateRelation :: (?spec::Spec) => Relation -> [Expr] -> RelInst
