{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module TVarValidate(validateVar, 
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
import ExprOps
import ExprValidate

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
                          ?privoverride = False
                      validateExpr' e
                      checkTypeMatch (typ v) e
         _      -> return ()


