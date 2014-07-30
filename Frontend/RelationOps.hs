{-# LANGUAGE ImplicitParams #-}
module Frontend.RelationOps (rargType) where

import Frontend.Relation
import Frontend.NS
import Frontend.Type
import Frontend.Spec

rargType :: (?spec::Spec, ?scope::Scope) => RArg -> Type
rargType = Type ?scope . tspec


