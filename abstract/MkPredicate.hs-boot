{-# LANGUAGE ImplicitParams #-}

module MkPredicate where

import Predicate
import ISpec

mkAtom :: (?spec::Spec) => RelOp -> PTerm -> PTerm -> Either Bool Predicate
