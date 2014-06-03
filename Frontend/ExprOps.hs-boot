{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Frontend.ExprOps where

import Frontend.Spec
import Frontend.Expr
import Frontend.Template
import Frontend.Method
import Frontend.NS
import Pos
import Frontend.Type

evalInt :: (?spec::Spec, ?scope::Scope) => ConstExpr -> Integer

isConstExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
isLExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
isMemExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
isLocalLHS :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
isInstExpr :: (?spec::Spec, ?scope::Scope) => Expr -> Bool
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
