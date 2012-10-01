{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module ExprOps where

import Control.Monad.Error
import Spec
import Expr
import Template
import Method
import NS
import Pos
import Type

evalInt :: (?spec::Spec, ?scope::Scope) => ConstExpr -> Integer

isConstExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
isLExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
isLocalLHS :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
exprNoSideEffects :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
exprObjs :: (?spec::Spec, ?scope::Scope) => Expr -> [Obj]
exprObjsRec :: (?spec::Spec, ?scope::Scope) => Expr -> [Obj]

--validateExpr :: (?spec::Spec, MonadError String me) => Scope -> Expr -> me ()
--validateExpr' :: (?spec::Spec, ?scope::Scope, MonadError String me) => Expr -> me ()

--validateCall :: (?spec::Spec, ?scope::Scope, MonadError String me) => Pos -> MethodRef -> [Expr] -> me ()


instance (?spec::Spec,?scope::Scope) => WithType Expr
instance (?spec::Spec,?scope::Scope) => WithTypeSpec Expr

mapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> Expr -> Expr
exprCallees :: (?spec::Spec) => Scope -> Expr -> [(Pos, (Template, Method))]
