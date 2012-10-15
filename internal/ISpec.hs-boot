{-# LANGUAGE ImplicitParams #-}

module ISpec where

import IType
import IVar

data Spec

getEnum :: (?spec::Spec) => String -> Enumeration
getVar :: (?spec::Spec) => String -> Var

