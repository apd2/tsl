{-# LANGUAGE ImplicitParams #-}

module ISpec where

import IType
import IVar

data Spec

getEnumeration :: (?spec::Spec) => String -> Enumeration
getEnumerator :: (?spec::Spec) => String -> Enumeration
getVar :: (?spec::Spec) => String -> Var

