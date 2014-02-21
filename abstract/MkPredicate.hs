{-# LANGUAGE ImplicitParams #-}

module MkPredicate (mkPRel) where

import Predicate
import BVSMT
import ISpec
import IExpr
import IType


-- Assumes that all dereference operations have already been expanded
mkPRel :: (?spec::Spec) => String -> [Expr] -> Predicate
mkPRel r as = PRel r $ map exprNormalise as

-- Apply bvTermNormalise to scalar sub-terms of the expression
exprNormalise :: (?spec::Spec) => Expr -> Expr
exprNormalise = mapExpr exprNormalise'

exprNormalise' :: (?spec::Spec) => Expr -> Expr
exprNormalise' e = case typ e of
                        UInt _ -> e'
                        SInt _ -> e'
                        _      -> e
    where e' = termToExpr $ bvTermNormalise $ scalarExprToTerm e
