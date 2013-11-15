{-# LANGUAGE ImplicitParams #-}

module MkPredicate where

import Predicate
import ISpec
import IExpr

mkPAtom :: (?spec::Spec) => RelOp -> PTerm -> PTerm -> Either Bool Predicate
mkPRel :: (?spec::Spec) => String -> [Expr] -> Predicate
