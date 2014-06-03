{-# LANGUAGE ImplicitParams #-}
module Frontend.RelationOps () where

import Frontend.Relation
import Frontend.NS
import Frontend.Type
import Frontend.Spec

instance (?spec::Spec, ?scope::Scope) => WithType RArg where
    typ = Type ?scope . tspec


