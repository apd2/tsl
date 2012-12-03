{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module TVarOps(varMapExpr,
               validateVar, 
               validateVar2) where

import Control.Monad.Error

import TSLUtil
import Pos
import Name
import Spec
import NS
import TVar
import Type
import TypeOps
import TypeValidate
import Expr
import {-# SOURCE #-} ExprOps
import ExprValidate

varMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> Var -> Var
varMapExpr f s v = Var (pos v) (varMem v) (tspecMapExpr f s $ tspec v) (name v) (fmap (mapExpr f s) $ varInit v)


instance (?spec::Spec, ?scope::Scope) => WithType Var where
    typ = Type ?scope . tspec

validateVar :: (?spec::Spec, MonadError String me) => Scope -> Var -> me ()
validateVar s v = do
    case varType v of
         EnumSpec p _ -> err p $ "Enumeration declared inside variable declaration. Use typedef instead."
         _            -> return ()
    validateTypeSpec s (tspec v)

validateVar2 :: (?spec::Spec, MonadError String me) => Scope -> Var -> me ()
validateVar2 s v = do
    validateTypeSpec2 s (tspec v)
    case varInit v of
         Just e -> do let ?scope = s
                      validateExpr' e
                      checkTypeMatch (typ v) e
         _      -> return ()


