{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module VarOps(validateVar, validateVar2) where

import Control.Monad.Error

import Spec
import NS
import Var
import TypeSpec
import TypeSpecOps
import {-# SOURCE #-} ExprOps

instance (?spec::Spec, ?scope::Scope) => WithType Var where
    typ = Type ?scope . tspec

validateVar :: (?spec::Spec, MonadError String me) => Scope -> Var -> me ()
validateVar s v = validateTypeSpec s (tspec v)

validateVar2 :: (?spec::Spec, MonadError String me) => Scope -> Var -> me ()
validateVar2 s v = do
    validateTypeSpec2 s (tspec v)
    case varInit v of
         Just e -> do let ?scope = s
                      validateExpr' e
                      checkTypeMatch (typ v) e
         _      -> return ()


