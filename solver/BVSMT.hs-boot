{-# LANGUAGE ImplicitParams #-}

module BVSMT where

import ISpec
import IVar
import Predicate
import SMTSolver
import RefineCommon
import BFormulaTypes
import qualified Cudd.Imperative as C

bvRelNormalise :: (?spec::Spec) => RelOp -> PTerm -> PTerm -> Formula
bvTermNormalise :: (?spec::Spec) => Term -> Term
bvSolver :: Spec -> SMTSolver -> C.STDdManager s u -> TheorySolver s u AbsVar AbsVar Var
