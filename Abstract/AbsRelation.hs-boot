{-# LANGUAGE ImplicitParams #-}

module Abstract.AbsRelation where

import Internal.IRelation
import Abstract.Predicate
import Internal.IExpr
import Internal.ISpec
import Ops

type RelInst = (Predicate, [(LogicOp, Expr)])

instantiateRelation :: (?spec::Spec) => Relation -> [Expr] -> RelInst
