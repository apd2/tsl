{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module TVarOps(varMapExpr) where

import Control.Monad.Error

import TSLUtil
import Pos
import Name
import Spec
import NS
import TVar
import Type
import TypeOps
import Expr
import {-# SOURCE #-} ExprOps

varMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> Var -> Var
varMapExpr f s v = Var (pos v) (varMem v) (tspecMapExpr f s $ tspec v) (name v) (fmap (mapExpr f s) $ varInit v)


instance (?spec::Spec, ?scope::Scope) => WithType Var where
    typ = Type ?scope . tspec
