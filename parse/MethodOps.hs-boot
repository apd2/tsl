{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module MethodOps where

import Control.Monad.Error

import Spec
import Template
import Method
import Var
import Statement

methFullVar  :: (?spec::Spec)                       => Template -> Method -> [(Template,Method,Var)]
validateMeth :: (?spec::Spec, MonadError String me) => Template -> Method -> me ()
methFullBody :: (?spec::Spec)                       => Template -> Method -> Either (Maybe Statement, Maybe Statement) Statement

