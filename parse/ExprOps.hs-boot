{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module ExprOps where

import Control.Monad.Error
import Spec
import Expr
import NS

evalInt :: (?spec::Spec, ?scope::Scope) => ConstExpr -> Integer
isConstExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool

validateExpr :: (?spec::Spec, MonadError String me) => Scope -> Expr -> me ()
validateExpr' :: (?spec::Spec, ?scope::Scope, MonadError String me) => Expr -> me ()

instance (?spec::Spec,?scope::Scope) => WithType Expr
