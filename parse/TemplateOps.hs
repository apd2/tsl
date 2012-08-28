{-# LANGUAGE FlexibleContexts, ImplicitParams, TupleSections #-}

module TemplateOps(tmParents,
                   validateTmInstances,
                   validateTmInstances2,
                   validateTmInit2,
                   validateTmPorts,
                   validateTmDerives,
                   validateSpecDerives,
                   validateTmNS,
                   validateTmTypeDecls,
                   validateTmTypeDecls2,
                   validateTmConsts,
                   validateTmConsts2,
                   validateTmGVars,
                   validateTmGVars2,
                   validateTmWires,
                   validateTmWires2,
                   validateTmMethods2,
                   validateTmProcesses2,
                   validateTmGoals2) where

import Data.List
import Data.Maybe
import qualified Data.Set as S
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

-- Get parent templates
tmParents :: (?spec::Spec) => Template -> [Template]
tmParents t = map (getTemplate . drvTemplate) (tmDerive t)

checkConcreteTemplate :: (?spec::Spec, MonadError String me) => Template -> Pos -> me ()
checkConcreteTemplate t p = do
    let purem = filter (\m -> case methFullBody t m of
                                   Left  _ -> True
                                   Right _ -> False)
                       (tmAllMethod t)
        purew = filter (isNothing . wireRHS) (tmAllWire t)
    assert (null purem) p $
           "Cannot instantiate pure template " ++ sname t ++ ". The following methods are not implemented: " ++ 
           (intercalate ", " $ map sname purem)
    assert (null purew) p $
           "Cannot instantiate pure template " ++ sname t ++ ". The following wires are not assigned: " ++ 
           (intercalate ", " $ map sname purew)


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

-----------------------------------------------------------
-- Validate template instances
-- * Every instance refers to a valid template and takes
--   correct number and types of arguments
-- Second pass: 
-- * only concrete templates can be instantiated
-----------------------------------------------------------

-- Validate template instantiation statement
-- * template name is valid
-- * correct number and types of parameters
validateInstance :: (?spec::Spec, MonadError String me) => Template -> Instance -> me ()
validateInstance tm i = do
    checkTemplate $ instTemplate i
    let t = getTemplate $ instTemplate i
    assert ((length $ tmPort t) == (length $ instPort i)) (pos i) $ 
           "Incorrect number of parameters to template " ++ sname t ++ 
           ". " ++ (show $ length $ tmPort t) ++ " parameters required."
    mapM (\(p,n) -> do ptm <- tmLookupPortInst tm n
                       assert (portTemplate p == ptm) (pos n) $ 
                              "Invalid template parameter: expected template type: " ++ (show $ portTemplate p) ++ ", actual type: " ++ show ptm)
         (zip (tmPort t) (instPort i))
    return ()


validateTmInstances :: (?spec::Spec,MonadError String me) => Template -> me ()
validateTmInstances tm = do {mapM (validateInstance tm) (tmInst tm); return()}

validateInstance2 :: (?spec::Spec, MonadError String me) => Template -> Instance -> me ()
validateInstance2 tm i = 
    checkConcreteTemplate (getTemplate $ instTemplate i) (pos i)

validateTmInstances2 :: (?spec::Spec,MonadError String me) => Template -> me ()
validateTmInstances2 tm = do {mapM (validateInstance2 tm) (tmInst tm); return()}


-----------------------------------------------------------
-- Validate template port
-- * port refers to a valid template 
-----------------------------------------------------------

validatePort :: (?spec::Spec, MonadError String me) => Template -> Port -> me ()
validatePort tm p = do {checkTemplate $ portTemplate p; return ()}

validateTmPorts :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmPorts tm = do {mapM (validatePort tm) (tmPort tm); return()}


-----------------------------------------------------------
-- Validate template derivation
-- 1. Validate each derive statement locally
-- 2. Validate the shape of the derivation graph (no cycles)
-----------------------------------------------------------

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

-- Validate the derivation graph of a spec
-- * no circular derivations
validateSpecDerives :: (?spec::Spec, MonadError String me) => me ()
validateSpecDerives = 
    case grCycle $ fst drvGraph of
         Nothing -> return ()
         Just c  -> err (pos $ snd $ head c) $ "Template derivation cycle: " ++ (intercalate "->" $ map (show . snd) c) 


-- Validate individual derive statement
validateDerive :: (?spec::Spec, MonadError String me) => Template -> Derive -> me ()
validateDerive tm d = do
    checkTemplate $ drvTemplate d
    let t = getTemplate $ drvTemplate d
    mapM (\p -> do case find ((== name p) . name) (tmPort tm) of
                        Nothing -> err (pos d) $ "Template " ++ sname t ++ " expects port " ++ sname p ++ 
                                                 ", but no such port is defined in template " ++ sname tm
                        Just p' -> assert (isDescendant (getTemplate $ portTemplate p) (getTemplate $ portTemplate p')) (pos d) $
                                          "Local port " ++ sname p' ++ " has type " ++ (show $ portTemplate p') ++ 
                                          ", but parent template " ++ sname t ++ " expects this port to be of type " ++ (show $ portTemplate p))
         (tmPort t)
    return ()

validateTmDerives :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmDerives tm = do {mapM (validateDerive tm) (tmDerive tm); return()}

------------------------------------------------------------------------------
-- Validate init blocks 
------------------------------------------------------------------------------

validateTmInit2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmInit2 t = do {mapM (validateExpr (ScopeTemplate t) . initBody) (tmInit t); return ()}


------------------------------------------------------------------------------
-- Validate goals at the second pass
------------------------------------------------------------------------------

validateGoal2 :: (?spec::Spec, MonadError String me) => Template -> Goal -> me ()
validateGoal2 t g = do
    let ?scope = ScopeTemplate t
    validateExpr' (goalCond g)
    assert (isBool $ goalCond g) (pos $ goalCond g) $ "Goal must be a boolean expression"

validateTmGoals2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmGoals2 t = do {mapM (validateGoal2 t) (tmGoal t); return ()}

------------------------------------------------------------------------------
-- Validate type decls
------------------------------------------------------------------------------
validateTmTypeDecls :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmTypeDecls tm = do {mapM (validateTypeSpec (ScopeTemplate tm) . tspec) (tmTypeDecl tm); return()}

validateTmTypeDecls2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmTypeDecls2 tm = do {mapM (validateTypeSpec2 (ScopeTemplate tm) . tspec) (tmTypeDecl tm); return()}

------------------------------------------------------------------------------
-- Validate constant declarations
------------------------------------------------------------------------------

validateTmConsts :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmConsts tm = do {mapM (validateConst (ScopeTemplate tm)) (tmConst tm); return()}

validateTmConsts2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmConsts2 tm = do {mapM (validateConst2 (ScopeTemplate tm)) (tmConst tm); return()}


------------------------------------------------------------------------------
-- Validate global variables
-- * First pass: validate type specs
-- * Second pass: validate initial assignment expressions; check that 
--   continuous assignment variables do not have initial assignments
------------------------------------------------------------------------------

validateGVar2 :: (?spec::Spec, MonadError String me) => Template -> GVar -> me ()
validateGVar2 tm v = validateVar2 (ScopeTemplate tm) (gvarVar v)

validateTmGVars :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmGVars tm = do {mapM (validateVar (ScopeTemplate tm) . gvarVar) (tmVar tm); return()}

validateTmGVars2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmGVars2 tm = do {mapM (validateGVar2 tm) (tmVar tm); return()}

------------------------------------------------------------------------------
-- Validate continuous assignments:
-- First pass:
-- * LHS must be a global variable
-- * LHSs must be unique
-- Second pass:
-- * RHS is a valid expressions of matching type
-- * no circular dependencies between continuous assignments
------------------------------------------------------------------------------

-- Find declaration of the wire inherited from a parent
wireParent :: (?spec::Spec) => Template -> Wire -> Maybe (Template, Wire)
wireParent t w = 
    case listToMaybe $ catMaybes $ map (\t' -> objLookup (ObjTemplate t') (name w)) (tmParents t) of
         Nothing                -> Nothing
         Just (ObjWire t' w')   -> Just (t',w')

-- Check if the wire overrides a derived declaration and, if so, 
-- make sure that its type matches previous declaration
validateWire :: (?spec::Spec, MonadError String me) => Template -> Wire -> me ()
validateWire t w = do
   case wireParent t w of
        Nothing      -> validateTypeSpec (ScopeTemplate t) (tspec w)
        Just (_,w')  -> assert (tspec w' == tspec w) (pos w) $ 
                               "Wire " ++ sname w ++ " was declared with type " ++ (show $ tspec w') ++ " at " ++ spos w' ++
                               " but s redefined as " ++ (show $ tspec w) ++ " at " ++ spos w

validateTmWires :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmWires t = do {mapM (validateWire t) (tmWire t); return ()}

validateWire2 :: (?spec::Spec, MonadError String me) => Template -> Wire -> me () 
validateWire2 t w = do
    let ?scope = ScopeTemplate t
    case wireRHS w of
         Just e  -> do validateExpr' e
                       checkTypeMatch (Type ?scope $ tspec w) e
         Nothing -> return ()

validateTmWires2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmWires2 t = do {mapM (validateWire2 t) (tmWire t); return ()}

------------------------------------------------------------------------------
-- Validate method declarations (only safe during the second pass)
------------------------------------------------------------------------------

validateTmMethods2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmMethods2 tm = do {mapM (validateMeth tm) (tmMethod tm); return ()}

------------------------------------------------------------------------------
-- Validate process declarations (only safe during the second pass)
------------------------------------------------------------------------------

validateTmProcesses2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmProcesses2 tm = do {mapM (validateProc tm) (tmProcess tm); return ()}

------------------------------------------------------------------------------
-- Validate template namespace
-- 1. No identifier is declared twice in a template
-- 2. Template-level declarations don't conflict with specification-level
--    declarations
-- 2. Template does not derive the same identifier from multiple parents
------------------------------------------------------------------------------

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

-- All identifiers visible as local names at the template level
--tmNamespace :: (?spec::Spec) => Template -> [Obj]
--tmNamespace t = specNamespace ++ tmLocalAndParentDecls t

-- * No identifier is declared twice in a template
-- * Template-level declarations don't conflict with specification-level
--   declarations
-- * No illegal overrides
validateTmNS :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmNS t = do
    let ns = tmLocalDecls t
    uniqNames (\n -> "Identifier " ++ n ++ " declared multiple times in template " ++ sname t) ns
    case mapMaybe (\o -> fmap (o,) $ find (\o' -> name o' == name o) specNamespace) ns of
         []       -> return ()
         (o,o'):_ -> err (pos o) $ "Identifier " ++ sname o ++ " conflicts with global declaration at " ++ spos o'
    checkTmOverrides t
    validateTmDeriveNS t


-- * derived template-level namespaces do not overlap
validateTmDeriveNS :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmDeriveNS t = do
    let nss = map (\d -> map (d,) $ tmLocalAndParentDecls $ getTemplate $ drvTemplate d) (tmDerive t)
    foldM (\names ns -> case intersectBy (\o1 o2 -> (name $ snd o1) == (name $ snd o2)) names ns of
                             []      -> return $ names++ns
                             (d,o):_ -> err (pos d) $ "Template " ++ sname t ++ " derives mutiple declarations of identifier " ++ sname o ++ 
                                                      " from the following templates: " ++ 
                                                      (intercalate ", " $ map (show . drvTemplate . fst) $ filter ((==name o) . name . snd) (names++ns)))
          [] nss
    return ()

-- * only methods, wires and ports can be overloaded
checkTmOverrides :: (?spec::Spec, MonadError String me) => Template -> me ()
checkTmOverrides t = do
    let local = tmLocalDecls t
        enviro = specNamespace ++ (concat $ map (tmLocalAndParentDecls . getTemplate . drvTemplate) (tmDerive t))
        override = filter (\(o1,o2) -> name o1 == name o2) $ (,) <$> local <*> enviro
    mapM (\(o1,o2) -> case (o1,o2) of
                           (ObjMethod _ m1, ObjMethod _ m2) -> return ()
                           (ObjPort _ p1,   ObjPort _ p2)   -> return ()
                           (ObjWire _ w1,   ObjWire _ w2)   -> return ()
                           _                                -> err (pos o1) $ "Identifier " ++ (sname o1) ++ " overrides previous declaration at " ++ spos o2)
         override
    return ()
