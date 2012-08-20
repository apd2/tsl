{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module ProcessOps() where

import Control.Monad.Error

import TSLUtil
import Name
import Spec
import Process
import Template
import Spec

validateProc :: (?spec::Spec, MonadError String me) => Template -> Process -> me ()
validateProc t p = do
    uniqNames (\n -> "Variable " ++ n ++ " declared multiple times in process " ++ sname p) 
              (procVar p)
