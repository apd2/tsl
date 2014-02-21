{-# LANGUAGE ImplicitParams #-}

module MkPredicate where

import Predicate
import ISpec
import IExpr

mkPRel :: (?spec::Spec) => String -> [Expr] -> Predicate
