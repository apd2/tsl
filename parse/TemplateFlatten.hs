{-# LANGUAGE ImplicitParams #-}

module TemplateFlatten(tmFlattenGVars,
                       tmFlattenWires,
                       tmFlattenInits,
                       tmFlattenProcs,
                       tmFlattenMeths,
                       tmFlattenGoals) where

import qualified Data.Tree as T
import Data.List

import Pos
import Name
import NS
import Var
import Spec
import Template
import TemplateOps
import StatementOps
import InstTree
import Process
import Method
import ExprFlatten

--------------------------------------------------------------------
-- Flattening individual template components
--------------------------------------------------------------------

tmFlattenGVars :: (?spec::Spec) => IID -> Template -> [GVar]
tmFlattenGVars iid tm = map (tmFlattenGVar iid tm) (tmVar tm)

tmFlattenGVar :: (?spec::Spec) => IID -> Template -> GVar -> GVar
tmFlattenGVar iid tm v = v{gvarVar = (gvarVar v){varName = itreeFlattenName iid (name v),
                                                 varInit = fmap (exprFlatten iid (ScopeTemplate tm)) (varInit $ gvarVar v)}}

tmFlattenWires :: (?spec::Spec) => IID -> Template -> [Wire]
tmFlattenWires iid tm = map (tmFlattenWire iid tm) (tmWire tm)

tmFlattenWire :: (?spec::Spec) => IID -> Template -> Wire -> Wire
tmFlattenWire iid tm w = w { wireName = itreeFlattenName iid (name w)
                           , wireRHS  = fmap (exprFlatten iid (ScopeTemplate tm)) (wireRHS w)}

tmFlattenInits :: (?spec::Spec) => IID -> Template -> [Init]
tmFlattenInits iid tm = map (tmFlattenInit iid tm) (tmInit tm)

tmFlattenInit :: (?spec::Spec) => IID -> Template -> Init -> Init
tmFlattenInit iid tm i = i {initBody = exprFlatten iid (ScopeTemplate tm) (initBody i)}

tmFlattenProcs :: (?spec::Spec) => IID -> Template -> [Process]
tmFlattenProcs iid tm = map (tmFlattenProc iid tm) (tmProcess tm)

tmFlattenProc :: (?spec::Spec) => IID -> Template -> Process -> Process
tmFlattenProc iid tm p = p { procName      = itreeFlattenName iid (name p)
                           , procStatement = statFlatten iid (ScopeProcess tm p) (procStatement p)}

tmFlattenMeths :: (?spec::Spec) => IID -> Template -> [Method]
tmFlattenMeths iid tm = map (tmFlattenMeth iid tm) (tmMethod tm)

tmFlattenMeth :: (?spec::Spec) => IID -> Template -> Method -> Method
tmFlattenMeth iid tm m = m { methName = itreeFlattenName iid (name m)
                           , methBody = case methBody m of
                                             Right s -> Right $ statFlatten iid (ScopeMethod tm m) s}

tmFlattenGoals :: (?spec::Spec) => IID -> Template -> [Goal]
tmFlattenGoals iid tm = map (tmFlattenGoal iid tm) (tmGoal tm)

tmFlattenGoal :: (?spec::Spec) => IID -> Template -> Goal -> Goal
tmFlattenGoal iid tm g = g { goalName = itreeFlattenName iid (name g)
                           , goalCond = exprFlatten iid (ScopeTemplate tm) (goalCond g)}
