{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module TypeSpecOps(typ', 
                   typeMatch,
                   typeComparable,
                   typeWidth,
                   isInt, isBool, isPtr, isArray, isStruct,
                   validateTypeSpec) where

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
import NS
--import ExprOps

typ' :: (?spec::Spec, WithType a) => a -> Type
typ' x = case typ x of
              (UserTypeSpec _ n,s) -> let (d,s') = getTypeDecl s n
                                      in typ' (tspec d,s')
              t                    -> t

isInt :: (?spec::Spec, WithType a) => a -> Bool
isInt x = case fst $ typ' x of
                 SIntSpec _ _ -> True
                 UIntSpec _ _ -> True
                 _            -> False

isBool :: (?spec::Spec, WithType a) => a -> Bool
isBool x = case fst $ typ' x of
                BoolSpec _ -> True
                _          -> False

isPtr :: (?spec::Spec, WithType a) => a -> Bool
isPtr x = case fst $ typ' x of
               PtrSpec _ _ -> True
               _           -> False

isArray :: (?spec::Spec, WithType a) => a -> Bool
isArray x = case fst $ typ' x of
               ArraySpec _ _ _ -> True
               _               -> False

isStruct :: (?spec::Spec, WithType a) => a -> Bool
isStruct x = case fst $ typ' x of
               StructSpec _ _ -> True
               _              -> False


-- Types can substitute each other in an expression.
typeMatch :: (?spec::Spec, WithType a, WithType b) => a -> b -> Bool
typeMatch x y = error "Not implemented: typeMatch"

-- Objects of these types can be compared using == and !=
typeComparable :: (?spec::Spec, WithType a, WithType b) => a -> b -> Bool
typeComparable x y = error "Not implemented: typeComparable"

typeWidth :: (?spec::Spec, WithType a) => a -> Int
typeWidth x = case fst $ typ' x of
                   SIntSpec _ w -> w
                   UIntSpec _ w -> w
                   _            -> error $ "typeWidth: non-integral type"

---------------------------------------------------------------------
-- Validate individual TypeSpec
---------------------------------------------------------------------

validateTypeSpec :: (?spec::Spec, MonadError String me) => Scope -> TypeSpec -> me ()

-- * Struct fields must have unique names and valid types
validateTypeSpec scope (StructSpec _ fs) = do
    uniqNames (\n -> "Field " ++ n ++ " declared multiple times ") fs
    mapM (validateTypeSpec scope . tspec) fs
    return ()

-- * user-defined type names refer to valid types
validateTypeSpec scope (UserTypeSpec _ n) = do {checkTypeDecl scope n; return ()}

validateTypeSpec scope _ = return ()

---------------------------------------------------------------------
-- Check that the graph of dependencies among TypeDecl's is acyclic
---------------------------------------------------------------------

type TDeclGraph = G.Gr StaticSym ()

gTypeName :: (TypeDecl,Scope) -> GStaticSym
gTypeName (d,ScopeTop)        = [name d]
gTypeName (d,ScopeTemplate t) = [name t,name d]

tdeclDeps :: (?spec::Spec) => GStaticSym -> [GStaticSym]
tdeclDeps n = (\(d,s) -> typeDeps (tspec d,s)) $ getTypeDecl ScopeTop n

typeDeps :: (?spec::Spec) => Type -> [GStaticSym]
typeDeps (StructSpec _ fs, s) = concat $ 
    map ((\t -> case t of
                     UserTypeSpec _ n -> [gTypeName $ getTypeDecl s n]
                     _                -> typeDeps (t,s)) . tspec)
        fs
typeDeps (UserTypeSpec _ n,s) = [gTypeName $ getTypeDecl s n]
typeDeps _                    = []


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
