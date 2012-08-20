{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module TypeSpecOps() where

import Control.Monad.Error
import Data.List
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G

import TSLUtil
import Name
import Pos
import TypeSpec
import Template
import Spec
import Ctx

---------------------------------------------------------------------
-- Validate individual TypeSpec
---------------------------------------------------------------------

validateTypeSpec :: (?spec::Spec, MonadError String me) => Ctx -> TypeSpec -> me ()

-- * Struct fields must have unique names and valid types
validateTypeSpec ctx (StructSpec _ fs) = do
    uniqNames (\n -> "Field " ++ n ++ " declared multiple times ") fs
    mapM (validateTypeSpec ctx . typ) fs
    return ()

-- * enumerator names must be unique in the current scope
validateTypeSpec ctx (EnumSpec _ es) = do
    mapM (ctxUniqName ctx . name) es
    return ()

-- * user-defined type names refer to valid types
validateTypeSpec ctx (UserTypeSpec _ n) = ctxCheckType ctx n

validateTypeSpec ctx _ = return ()

---------------------------------------------------------------------
-- Check that the graph of dependencies among TypeDecl's is acyclic
---------------------------------------------------------------------

type TDeclGraph = G.Gr StaticSym ()

tdeclDeps :: (?spec::Spec) => GStaticSym -> [GStaticSym]
tdeclDeps n = (\(t,c) -> typeDeps c (typ t)) $ ctxGetType CtxTop n

typeDeps :: (?spec::Spec) => Ctx -> TypeSpec -> [GStaticSym]
typeDeps c (StructSpec _ fs) = concat $ 
    map ((\t -> case t of
                     UserTypeSpec _ n -> [ctxGTypeName $ ctxGetType c n]
                     _                -> typeDeps c t) . typ)
        fs
typeDeps c (UserTypeSpec _ n) = [ctxGTypeName $ ctxGetType c n]
typeDeps _ _ = []


-- construct dependency graph
tdeclGraph :: (?spec::Spec) => TDeclGraph
tdeclGraph = 
    let tnames = map ((\n -> [n]) . name) (specType ?spec) ++ 
                 (concat $ map (\t -> map (\d -> [name t, name d]) $ tmTypeDecl t) $ specTemplate ?spec)
        tmap = M.fromList $ zip tnames [1..]
        gnodes = foldl' (\g (t,id) -> G.insNode (id, t) g) G.empty (M.toList tmap)
    in foldl' (\g n -> foldl' (\g d -> G.insEdge (tmap M.! n, tmap M.! d, ()) g) 
                              g (tdeclDeps n))
              gnodes tnames

validateTypeDecls :: (?spec::Spec, MonadError String me) => me ()
validateTypeDecls = 
    case grCycle tdeclGraph of
         Nothing -> return ()
         Just c  -> err (pos $ snd $ head c) $ "Cyclic type aggregation: " ++ (intercalate "->" $ map (show . snd) c) 
