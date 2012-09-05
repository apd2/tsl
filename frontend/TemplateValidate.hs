{-# LANGUAGE FlexibleContexts, ImplicitParams, TupleSections #-}

module TemplateValidate(checkConcreteTemplate,
                        validateTmInstances,
                        validateTmInstances2,
                        validateTmInit2,
                        validateTmPorts,
                        validateTmDerives,
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
import qualified Data.Map as M
import Control.Monad.Error
import Control.Applicative

import TSLUtil
import Pos
import Name
import Type
import TypeOps
import TypeValidate
import Template
import TemplateOps
import Spec
import ConstOps
import Var
import VarOps
import ExprOps
import ExprValidate
import Method
import MethodOps
import Process
import ProcessOps
import NS

checkConcreteTemplate :: (?spec::Spec, MonadError String me) => Template -> Pos -> me ()
checkConcreteTemplate t p = do
    let (purem, purew) = tmPure t
    assert (null purem) p $
           "Cannot instantiate pure template " ++ sname t ++ ". The following methods are not implemented: " ++ 
           (intercalate ", " $ map sname purem)
    assert (null purew) p $
           "Cannot instantiate pure template " ++ sname t ++ ". The following wires are not assigned: " ++ 
           (intercalate ", " $ map sname purew)


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
-----------------------------------------------------------

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
validateGVar2 tm v = do let ?scope = ScopeTemplate tm
                        validateVar2 ?scope (gvarVar v)
                        case (varInit $ gvarVar v) of
                             Nothing -> return ()
                             Just e  -> assert (isConstExpr e) (pos e) $ "Initial value of a global variable must be a constant expression"

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
                       assert (exprNoSideEffects e) (pos e) "Wire expression must be side-effect free"
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
