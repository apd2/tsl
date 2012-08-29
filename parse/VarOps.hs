{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module VarOps(varMapExpr,
              validateVar, 
              validateVar2) where

import Control.Monad.Error

import Pos
import Name
import Spec
import NS
import Var
import TypeSpec
import TypeSpecOps
import Expr
import {-# SOURCE #-} ExprOps

varMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> Var -> Var
varMapExpr f s v = Var (pos v) (tspecMapExpr f s $ tspec v) (name v) (fmap (mapExpr f s) $ varInit v)


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


