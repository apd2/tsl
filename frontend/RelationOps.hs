{-# LANGUAGE ImplicitParams #-}
module RelationOps () where

import Relation
import NS
import Type
import Spec

instance (?spec::Spec, ?scope::Scope) => WithType RArg where
    typ = Type ?scope . tspec


