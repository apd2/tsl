{-# LANGUAGE ImplicitParams #-}

module ISpec where

import IType
import IVar

data Spec

getEnumeration :: (?spec::Spec) => String -> Enumeration
lookupEnumerator :: (?spec::Spec) => String -> Maybe Enumeration
getEnumerator :: (?spec::Spec) => String -> Enumeration
getVar :: (?spec::Spec) => String -> Var
typeWidth :: (?spec::Spec, Typed a) => a -> Int
