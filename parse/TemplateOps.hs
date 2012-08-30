{-# LANGUAGE FlexibleContexts, ImplicitParams, TupleSections #-}

module TemplateOps(tmMapExpr,
                   tmMapTSpec,
                   tmPure,
                   isConcreteTemplate,
                   drvGraph,
                   instGraph,
                   callGraph,
                   isDescendant,
                   tmParents,
                   tmAllGoal,
                   tmAllMethod,
                   tmAllProcess,
                   tmAllInit,
                   tmAllInst,
                   tmAllWire,
                   tmAllVar,
                   tmLookupPortInst,
                   tmLocalDecls,
                   tmLocalAndParentDecls,
                   tmScopes,
                   callees) where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.Error
import qualified Data.Graph.Inductive.Graph     as G
import qualified Data.Graph.Inductive.Tree      as G
import qualified Data.Graph.Inductive.Query.DFS as G
import Control.Applicative hiding (Const)

import TSLUtil
import Pos
import Name
import TypeSpec
import TypeSpecOps
import Template
import Spec
import Const
import ConstOps
import Var
import VarOps
import {-# SOURCE #-} MethodOps
import Expr
import {-# SOURCE #-} ExprOps
import Method
import Process
import ProcessOps
import StatementOps
import NS

-- Map function over all expressions occurring in the template
tmMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Template -> Template
tmMapExpr f tm = tm { tmConst    = map (\c -> c{constVal = mapExpr f s (constVal c)})                              (tmConst tm)
                    , tmTypeDecl = map (\t -> TypeDecl (pos t) (tspecMapExpr f s $ tspec t) (name t))              (tmTypeDecl tm)
                    , tmVar      = map (\v -> v{gvarVar = varMapExpr f s (gvarVar v)})                             (tmVar tm)
                    , tmWire     = map (\w -> w{wireType = tspecMapExpr f s (wireType w), 
                                                wireRHS  = fmap (mapExpr f s) (wireRHS w)})                        (tmWire tm)
                    , tmInit     = map (\i -> i{initBody = mapExpr f s (initBody i)})                              (tmInit tm)
                    , tmProcess  = map (\p -> p{procStatement = statMapExpr f s (procStatement p)})                (tmProcess tm)
                    , tmMethod   = map (\m -> m{methRettyp = fmap (tspecMapExpr f s) (methRettyp m),
                                                methArg    = map (\a -> a{argType = tspecMapExpr f s (argType a)}) (methArg m),
                                                methBody   = case methBody m of
                                                                  Left (mb,ma) -> Left  $ (fmap (statMapExpr f s) mb, fmap (statMapExpr f s) mb)
                                                                  Right b      -> Right $ statMapExpr f s b})      (tmMethod tm)
                    , tmGoal     = map (\g -> g{goalCond = mapExpr f s (goalCond g)})                              (tmGoal tm)}
    where s = ScopeTemplate tm

-- Map function over all TypeSpec's occurring in the template
tmMapTSpec :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Template -> Template
tmMapTSpec f tm = tm { tmConst    = map (\c -> Const (pos c) (mapTSpec f s $ tspec c) (name c) (constVal c))            (tmConst tm)
                     , tmTypeDecl = map (\t -> TypeDecl (pos t) (mapTSpec f s $ tspec t) (name t))                      (tmTypeDecl tm)
                     , tmVar      = map (\v -> v{gvarVar  = (gvarVar v){varType = mapTSpec f s $ tspec v}})             (tmVar tm)
                     , tmWire     = map (\w -> w{wireType = mapTSpec f s (wireType w)})                                 (tmWire tm)
                     , tmProcess  = map (\p -> p{procStatement = statMapTSpec f s (procStatement p)})                   (tmProcess tm)
                     , tmMethod   = map (\m -> m{methRettyp = fmap (mapTSpec f s) (methRettyp m),
                                                 methArg    = map (\a -> a{argType = mapTSpec f s (argType a)}) (methArg m),
                                                 methBody   = case methBody m of
                                                                   Left (mb,ma) -> Left  $ (fmap (statMapTSpec f s) mb, fmap (statMapTSpec f s) mb)
                                                                   Right b      -> Right $ statMapTSpec f s b})         (tmMethod tm)}
    where s = ScopeTemplate tm


tmPure :: (?spec::Spec) => Template -> ([Method],[Wire])
tmPure tm = (purem, purew)
    where purem = filter (\m -> case methFullBody tm m of
                                     Left  _ -> True
                                     Right _ -> False)
                         (tmAllMethod tm)
          purew = filter (isNothing . wireRHS) (tmAllWire tm)

isConcreteTemplate :: (?spec::Spec) => Template -> Bool
isConcreteTemplate t = case tmPure t of
                            ([],[]) -> True
                            _       -> False

-------------------------------------------------------------------
-- Instantiation graph
-------------------------------------------------------------------

type InstGraph = G.Gr Ident ()

instGraph :: (?spec::Spec) => InstGraph
instGraph = 
    let tmap = M.fromList $ zip (map name $ specTemplate ?spec) [1..]
        gnodes = foldl' (\g t -> G.insNode (tmap M.! name t, name t) g) G.empty (specTemplate ?spec)
        g = foldl' (\g t -> foldl' (\g i -> G.insEdge (tmap M.! name t, tmap M.! instTemplate i, ()) g)
                                   g (tmAllInst t))
                   gnodes (specTemplate ?spec)
    in g


-------------------------------------------------------------------
-- Derivation graph
-------------------------------------------------------------------

type DrvGraph = (G.Gr Ident (), M.Map Ident Int)


-- construct template derivation graph
drvGraph :: (?spec::Spec) => DrvGraph
drvGraph = 
    let tmap = M.fromList $ zip (map name $ specTemplate ?spec) [1..]
        gnodes = foldl' (\g t -> G.insNode (tmap M.! name t, name t) g) G.empty (specTemplate ?spec)
        g = foldl' (\g t -> foldl' (\g d -> G.insEdge (tmap M.! name t, tmap M.! drvTemplate d, ()) g)
                                   g (tmDerive t))
                   gnodes (specTemplate ?spec)
    in (g,tmap)


-------------------------------------------------------------------
-- Call graph
-------------------------------------------------------------------

type CallGraph = G.Gr Scope Pos

tmScopes :: (?spec::Spec) => Template -> [Scope]
tmScopes tm = (map (ScopeProcess tm) (tmAllProcess tm)) ++ (map (ScopeMethod tm) (tmAllMethod tm))

callees :: (?spec::Spec) => Scope -> [(Pos, (Template, Method))]
callees s@(ScopeProcess t p) = statCallees s (procStatement p)
callees s@(ScopeMethod t m)  = statCallees s b
    where Right b = methFullBody t m

callGraph :: (?spec::Spec) => CallGraph
callGraph = 
    let scopes = zip (concatMap tmScopes $ filter isConcreteTemplate $ specTemplate ?spec) [1..]
        smap = M.fromList scopes
        gnodes = foldl' (\g (s,id) -> G.insNode (id, s) g) G.empty scopes
        g = foldl' (\g (s,id) -> foldl' (\g (p,(t,m)) -> G.insEdge (id, smap M.! (ScopeMethod t m), p) g)
                                        g (callees s))
                   gnodes scopes
    in g


-------------------------------------------------------------------
-- Namespace-related stuff
-------------------------------------------------------------------


tmLocalDecls :: (?spec::Spec) => Template -> [Obj]
tmLocalDecls t = (map (ObjPort t)                     (tmPort t))     ++
                 (map (ObjConst (ScopeTemplate t))    (tmConst t))    ++
                 (map (ObjTypeDecl (ScopeTemplate t)) (tmTypeDecl t)) ++
                 (map (ObjGVar t)                     (tmVar t))      ++
                 (map (ObjWire t)                     (tmWire t))     ++
                 (map (ObjInstance t)                 (tmInst t))     ++
                 (map (ObjProcess t)                  (tmProcess t))  ++
                 (map (ObjMethod t)                   (tmMethod t))   ++
                 (map (ObjGoal t)                     (tmGoal t))     ++
                 (concat $ map (\d -> case tspec d of
                                           EnumSpec _ es -> map (ObjEnum (Type (ScopeTemplate t) $ tspec d)) es
                                           _             -> []) (tmTypeDecl t))


-- All objects declared in the template or inherited from parents
tmLocalAndParentDecls :: (?spec::Spec) => Template -> [Obj]
tmLocalAndParentDecls t = concat $ (tmLocalDecls t):parents
    where parents = map (tmLocalAndParentDecls . getTemplate . drvTemplate) (tmDerive t)


-- Get parent templates
tmParents :: (?spec::Spec) => Template -> [Template]
tmParents t = map (getTemplate . drvTemplate) (tmDerive t)

-- Find port or instance by name.  Returns the name of the associated template.
tmLookupPortInst :: (MonadError String me) => Template -> Ident -> me Ident
tmLookupPortInst t n = case listToMaybe $ catMaybes [p, i] of
                            Nothing -> err (pos n) $ "Unknown port or instance name " ++ show n
                            Just tn -> return tn
    where p = fmap (portTemplate) $ find ((== n) . name) (tmPort t)
          i = fmap (instTemplate) $ find ((== n) . name) (tmInst t)

isDescendant :: (?spec::Spec) => Template -> Template -> Bool
isDescendant anc des = 
    let (g,m) = drvGraph 
        ancid = m M.! (name anc)
        desid = m M.! (name des)
    in elem ancid (G.reachable desid g)


tmAllVar :: (?spec::Spec) => Template -> [GVar]
tmAllVar t = concatMap (\o -> case o of
                                    ObjGVar _ v -> [v]
                                    _           -> []) 
                       (tmLocalAndParentDecls t)

tmAllInst :: (?spec::Spec) => Template -> [Instance]
tmAllInst t = concatMap (\o -> case o of
                                    ObjInstance _ i -> [i]
                                    _               -> []) 
                        (tmLocalAndParentDecls t)

tmAllInit :: (?spec::Spec) => Template -> [Init]
tmAllInit t = tmInit t ++ (concat $ map tmAllInit (tmParents t))

tmAllProcess :: (?spec::Spec) => Template -> [Process]
tmAllProcess t = concatMap (\o -> case o of
                                    ObjProcess _ p -> [p]
                                    _              -> []) 
                           (tmLocalAndParentDecls t)

tmAllGoal :: (?spec::Spec) => Template -> [Goal]
tmAllGoal t = concatMap (\o -> case o of
                                    ObjGoal _ g -> [g]
                                    _           -> []) 
                        (tmLocalAndParentDecls t)

tmAllMethod :: (?spec::Spec) => Template -> [Method]
tmAllMethod t = map (\(t,m) -> m{methBody = methFullBody t m}) $ tmAllMethod' t
                
tmAllMethod' :: (?spec::Spec) => Template -> [(Template,Method)]
tmAllMethod' t = (map (t,) $ tmMethod t) ++
                 (filter (\(_,m) -> not $ elem (name m) $ (map name $ tmMethod t)) $ 
                         concat $ map tmAllMethod' (tmParents t))

tmAllWire :: (?spec::Spec) => Template -> [Wire]
tmAllWire t = tmWire t ++
              (filter (\w -> not $ elem (name w) $ (map name $ tmWire t)) $ 
                      concat $ map tmAllWire (tmParents t))
