{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module ExprOps where

import Control.Monad.Error
import Spec
import Expr
import NS
import Pos

evalInt :: (?spec::Spec, ?scope::Scope) => ConstExpr -> Integer

isConstExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
isLExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
exprNoSideEffects :: (?spec::Spec, ?scope::Scope) => Expr -> Bool

validateExpr :: (?spec::Spec, MonadError String me) => Scope -> Expr -> me ()
validateExpr' :: (?spec::Spec, ?scope::Scope, MonadError String me) => Expr -> me ()

validateCall :: (?spec::Spec, ?scope::Scope, MonadError String me) => Pos -> MethodRef -> [Expr] -> me ()


instance (?spec::Spec,?scope::Scope) => WithType Expr
