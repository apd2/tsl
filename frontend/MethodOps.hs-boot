{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module MethodOps where

import Control.Monad.Error

import Spec
import Template
import Method
import TVar
import Statement
import Name

methLabels   :: (?spec::Spec) => Method -> [Ident]
methFullVar  :: (?spec::Spec)                       => Template -> Method -> [(Template,Method,Var)]
methFullBody :: (?spec::Spec)                       => Template -> Method -> Either (Maybe Statement, Maybe Statement) Statement

