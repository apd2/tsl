{-# LANGUAGE ImplicitParams #-}

module MkPredicate where

import Predicate
import ISpec
import IExpr

mkPRel :: (?spec::Spec) => String -> [Expr] -> Predicate
scalarExprToTerm :: (?spec::Spec) => Expr -> Term
scalarExprToTerm' :: Expr -> Term
valToTerm :: Val -> Term
termPad :: (?spec::Spec) => Int -> Term -> Term
