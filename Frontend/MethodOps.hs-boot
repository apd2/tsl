{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Frontend.MethodOps where

import Frontend.Spec
import Frontend.Template
import Frontend.Method
import Frontend.TVar
import Frontend.Statement
import Name

methLabels   :: (?spec::Spec) => Method -> [Ident]
methFullVar  :: (?spec::Spec)                       => Template -> Method -> [(Template,Method,Var)]
methFullBody :: (?spec::Spec)                       => Template -> Method -> Either (Maybe Statement, Maybe Statement) Statement

