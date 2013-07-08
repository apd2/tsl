{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module ConstOps(validateConst,
                validateConst2) where

import Control.Monad.Error

import TSLUtil
import Pos
import Type
import TypeOps
import TypeValidate
import {-# SOURCE #-} ExprOps
import ExprValidate
import Const
import Spec
import NS

instance (?spec::Spec,?scope::Scope) => WithType Const where
    typ = Type ?scope . tspec

-- First pass: validate types
validateConst :: (?spec::Spec, MonadError String me) => Scope -> Const -> me ()
validateConst s c = validateTypeSpec s (tspec c)

-- Second pass: validate value expressions
validateConst2 :: (?spec::Spec, MonadError String me) => Scope -> Const -> me ()
validateConst2 s c = do
    let ?scope = s
        ?privoverride = False
    let v = constVal c
    validateTypeSpec2 s (tspec c)
    validateExpr' v
    checkTypeMatch c v
    assert (isConstExpr v) (pos v) $ "Non-constant expression in constant declaration"
