{-# LANGUAGE ImplicitParams #-}

module ExprOps where

import Spec
import Expr
import NS

evalInt :: (?spec::Spec, ?scope::Scope) => ConstExpr -> Integer

