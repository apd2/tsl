{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module ProcessOps(validateProc) where

import Control.Monad.Error

import TSLUtil
import Name
import Spec
import Process
import Template
import Spec
import StatementOps
import NS

validateProc :: (?spec::Spec, MonadError String me) => Template -> Process -> me ()
validateProc t p = do
    uniqNames (\n -> "Variable " ++ n ++ " declared multiple times in process " ++ sname p) 
              (procVar p)
    let ?privoverride = False in validateStat (ScopeProcess t p) (procStatement p)
