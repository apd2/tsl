{-# LANGUAGE ImplicitParams #-}

module Frontend.TemplateFlatten(tmFlattenGVars,
                       tmFlattenWires,
                       tmFlattenInits,
                       tmFlattenPrefixes,
                       tmFlattenProcs,
                       tmFlattenMeths,
                       tmFlattenGoals,
                       tmFlattenRels, 
                       tmFlattenApps,
                       WireGraph,
                       wireGraph) where

import qualified Data.Map  as M
import Data.List
import Data.Maybe
import qualified Data.Graph.Inductive.Graph     as G
import qualified Data.Graph.Inductive.Tree      as G

import Name
import Frontend.NS
import Frontend.TVar
import Frontend.Spec
import Frontend.Template
import Frontend.StatementOps
import Frontend.InstTree
import Frontend.Process
import Frontend.Method
import Frontend.ExprOps
import Frontend.ExprFlatten
import Frontend.Relation

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

tmFlattenPrefixes :: (?spec::Spec) => IID -> Template -> [Prefix]
tmFlattenPrefixes iid tm = map (tmFlattenPrefix iid tm) (tmPrefix tm)

tmFlattenPrefix :: (?spec::Spec) => IID -> Template -> Prefix -> Prefix
tmFlattenPrefix iid tm a = a {prefBody = statFlatten iid (ScopeTemplate tm) (prefBody a)}

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

tmFlattenRels :: (?spec::Spec) => IID -> Template -> [Relation]
tmFlattenRels iid tm = map (tmFlattenRel iid tm) (tmRelation tm)

tmFlattenRel :: (?spec::Spec) => IID -> Template -> Relation -> Relation
tmFlattenRel iid tm r = r { relName = itreeFlattenName iid (name r)
                          , relRule = map (\rl -> rl{ruleExpr = exprFlatten iid (ScopeRelation tm r) $ ruleExpr rl}) (relRule r)}

tmFlattenApps :: (?spec::Spec) => IID -> Template -> [Apply]
tmFlattenApps iid tm = map (tmFlattenApp iid tm) (tmApply tm)

tmFlattenApp :: (?spec::Spec) => IID -> Template -> Apply -> Apply
tmFlattenApp iid tm a = a { applyRel = itreeFlattenName iid (applyRel a)
                          , applyArg = map (exprFlatten iid (ScopeTemplate tm)) (applyArg a)}

--------------------------------------------------------------------
-- Operations on flattened template
--------------------------------------------------------------------

type WireGraph = G.Gr Ident ()

wireGraph :: (?spec::Spec) => WireGraph
wireGraph = 
    let t = head $ specTemplate ?spec
        wmap = M.fromList $ zip (map name $ tmWire t) [1..]
        gnodes = M.foldlWithKey (\g w id -> G.insNode (id, w) g) G.empty wmap
    in foldl' (\g w -> foldl' (\g w' -> G.insEdge (wmap M.! name w, wmap M.! name w', ()) g) 
                              g (wireDeps w))
              gnodes (tmWire t)

wireDeps :: (?spec::Spec) => Wire -> [Wire]
wireDeps w = 
    let t = head $ specTemplate ?spec
    in let ?scope = ScopeTemplate t
       in mapMaybe (\o -> case o of
                               ObjWire t w -> Just w
                               _           -> Nothing) 
                   $ exprObjs $ fromJust $ wireRHS w
