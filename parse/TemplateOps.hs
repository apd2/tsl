{-# LANGUAGE FlexibleContexts, ImplicitParams, TupleSections #-}

module TemplateOps(drvGraph,
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
                   tmLocalAndParentDecls) where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.Error
import qualified Data.Graph.Inductive.Graph     as G
import qualified Data.Graph.Inductive.Tree      as G
import qualified Data.Graph.Inductive.Query.DFS as G
import Control.Applicative

import TSLUtil
import Pos
import Name
import TypeSpec
import TypeSpecOps
import Template
import Spec
import ConstOps
import Var
import VarOps
import {-# SOURCE #-} MethodOps
import {-# SOURCE #-} ExprOps
import Method
import Process
import ProcessOps
import NS

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

--tmAllAssign :: (?spec::Spec) => Template -> [ContAssign]
--tmAllAssign t = tmAssign t ++ (concat $ map tmAllAssign (tmParents t))

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


-- Merge template with its parents
tmMergeParents :: (?spec::Spec) => Template -> Template
tmMergeParents tm = Template (pos tm)
                             (name tm)
                             (tmPort tm)
                             []                    -- tmDerive
                             []                    -- tmConst
                             []                    -- tmTypeDecl
                             (tmAllVar tm)
                             (tmAllWire tm)
                             (tmAllInst tm)
                             (tmAllInit tm)
                             (tmAllProcess tm)
                             (tmAllMethod tm)
                             (tmAllGoal tm)


