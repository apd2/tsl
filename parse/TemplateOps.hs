{-# LANGUAGE FlexibleContexts, ImplicitParams #-}

module TemplateOps() where

import Data.List
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.Error
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G

import TSLUtil
import Pos
import Name
import TypeSpec
import Template
import Spec
import NS

-- Find port or instance by name.  Returns the name of the associated template.
tmLookupPortInst :: (MonadError String me) => Template -> Ident -> me Ident
tmLookupPortInst t n = case listToMaybe $ catMaybes [p, i] of
                            Nothing -> err (pos n) $ "Invalid port or instance name " ++ show n
                            Just tn -> return tn
    where p = fmap (portTemplate) $ find ((== n) . name) (tmPort t)
          i = fmap (instTemplate) $ find ((== n) . name) (tmInst t)


-----------------------------------------------------------
-- Validate template derivation
-- 1. Validate each derive statement locally
-- 2. Validate the shape of the derivation graph (no cycles)
-----------------------------------------------------------

type DrvGraph = G.Gr (Ident) ()

-- construct template derivation graph
drvGraph :: (?spec::Spec) => DrvGraph
drvGraph = 
    let tmap = M.fromList $ zip (map name $ specTemplate ?spec) [1..]
        gnodes = foldl' (\g t -> G.insNode (tmap M.! name t, name t) g) G.empty (specTemplate ?spec)
    in foldl' (\g t -> foldl' (\g d -> G.insEdge (tmap M.! name t, tmap M.! drvTemplate d, ()) g) 
                              g (tmDerive t))
              gnodes (specTemplate ?spec)


-- Validate the derivation graph of a spec
-- * no circular derivations
validateDerives :: (?spec::Spec, MonadError String me) => me ()
validateDerives = 
    case grCycle drvGraph of
         Nothing -> return ()
         Just c  -> err (pos $ snd $ head c) $ "Template derivation cycle: " ++ (intercalate "->" $ map (show . snd) c) 


-- Validate individual derive statement
-- * derives refer to valid template names
-- * derives get correct number and types of parameters
validateDerive :: (?spec::Spec, MonadError String me) => Template -> Derive -> me ()
validateDerive tm d = do
    specCheckTemplate (drvTemplate d)
    let t = specGetTemplate (drvTemplate d)
    if (length $ tmPort t) /= (length $ drvPort d) 
       then err (pos d) $ "Invalid number of parameters to derived template " ++ (show $ name t) ++ 
                          ". " ++ (show $ length $ tmPort t) ++ " parameters required."
       else return ()
    mapM (\(p,n) -> do ptm <- tmLookupPortInst tm n
                       if (portTemplate p /= ptm)
                          then err (pos n) $ "Invalid template parameter: expected template type: " ++ 
                                             (show $ portTemplate p) ++ ", actual type: " ++ show ptm
                          else return ())
         (zip (tmPort t) (drvPort d))
    return ()

------------------------------------------------------------------------------
-- Validate template namespace
-- 1. No identifier is declared twice in a template
-- 2. Template-level declarations don't conflict with specification-level
--    declarations
-- 2. Template does not derive the same identifier from multiple parents
------------------------------------------------------------------------------

-- All objects declared in the template or inherited from parents
tmNamespace :: (?spec::Spec) => Template -> [Obj]
tmNamespace t = local:parents
    where parents = map (tmNamespace . specGetTemplate . drvTemplate) (tmDerive t)
          local = (map ObjPort     (tmPort t)) ++
                  (map ObjConst    (tmConst t)) ++
                  (map ObjTypeDecl (tmTypeDecl t)) ++
                  (map ObjGVar     (tmVar t)) ++
                  (map ObjInstance (tmInst t)) ++
                  (map ObjProcess  (tmProcess t)) ++
                  (map ObjMethod   (tmMethod t)) ++
                  (concat $ map (\t -> case typ t of
                                            EnumSpec _ es -> map ObjEnum es
                                            _             -> []) (tmTypeDecl t))

-- * No identifier is declared twice in a template
-- * Template-level declarations don't conflict with specification-level
--   declarations
validateTmNS :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmNS t = do
    let ns = tmNamespace t
    case filter ((> 1) . length) $ groupBy (\o1 o2 -> name o1 == name o2) ns of
         []      -> return ()
         g@(o:_) -> err (pos o) $ "Identifier " ++ (show $ name o) ++ " declared more than once in template " ++ (show $ name t) ++
                                  "at locations:\n  " ++ (intercalate "\n  " $ map (show . pos) g)
    case filter (\o -> find (\o' -> name o' == name o) specNamespace) ns 

-- * derived template-level namespaces do not overlap
validateTmDeriveNS :: (?spec::Spec, MonadError String me) => Ctx -> Template -> me ()
validateTmDeriveNS c t = do
    let nss = map (\d -> map (name d,) $ tmNamespace $ specGetTemplate $ drvTemplate d) (tmDerive t)
    foldM (\names ns -> case intersectBy (\o1 o2 -> (name $ snd o1) == (name $ snd o2)) names ns of
                             []     -> return $ names++ns
                             (n,o)  -> err (pos ) $ )
          [] nss



