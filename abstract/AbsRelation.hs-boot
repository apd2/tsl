{-# LANGUAGE ImplicitParams #-}

module AbsRelation where

import IRelation
import Predicate
import IExpr
import ISpec
import Ops

type RelInst = (Predicate, [(LogicOp, Expr)])

instantiateRelation :: (?spec::Spec) => Relation -> [Expr] -> RelInst
