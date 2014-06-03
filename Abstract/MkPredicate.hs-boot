{-# LANGUAGE ImplicitParams #-}

module Abstract.MkPredicate where

import Abstract.Predicate
import Internal.ISpec
import Internal.IExpr

mkPRel :: (?spec::Spec) => String -> [Expr] -> Predicate
scalarExprToTerm :: (?spec::Spec) => Expr -> Term
scalarExprToTerm' :: Expr -> Term
valToTerm :: Val -> Term
termPad :: (?spec::Spec) => Int -> Term -> Term
