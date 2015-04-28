{-# LANGUAGE PolymorphicComponents, RecordWildCards, ScopedTypeVariables, TemplateHaskell, FlexibleContexts, ConstraintKinds, ImplicitParams #-}

module Solver.BVSMT where

import Internal.ISpec
import Internal.IVar
import Abstract.Predicate
import Solver.SMTSolver
import Synthesis.RefineCommon
import Abstract.BFormulaTypes
import qualified Cudd.Imperative as C

bvRelNormalise :: (?spec::Spec) => RelOp -> PTerm -> PTerm -> Formula
bvTermNormalise :: (?spec::Spec) => Term -> Term
bvSolver :: RM s u rm => Spec -> SMTSolver -> C.DDManager s u -> TheorySolver s u AbsVar AbsVar Var rm
