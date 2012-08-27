{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module SpecOps(specNamespace) where

import Data.List
import Data.Maybe
import Control.Monad.Error

import TSLUtil
import TypeSpec
import TypeSpecOps
import Pos
import Name
import Spec
import NS
import Template
import TemplateOps
import Const
import ConstOps

-- Main validation function
--
-- Validation order:
--
-- First pass:
-- * Validate top-level namespace
-- * Validate template instances (required by derive statements)
-- * Validate template ports (required by derive statements)
-- * Validate derive statements (required to build template namespaces)
-- * Validate template namespaces
-- * Validate type decls (but not array sizes)
-- * Validate constant types (but not initial assignments)
-- * Validate global variable types (but not initial assignments)
-- * Validate continuous assignments (LHS only)
--
-- Second pass: We are now ready to validate components of the specification containing expressions:
-- * Validate method declarations
-- * Validate call graph (no recursion, all possible stacks are valid (only invoke methods allowed in this context))
-- * Validate process declarations
-- * Validate initial assignment expressions in constant declarations
-- * Validate array size declarations (must be constant)
-- * Validate initial variable assignments
-- * Validate process and method bodies
-- * Validate RHS of continous assignments; check acyclicity of cont assignments
-- * Validate goals
-- From now on, check that
validateSpec :: (MonadError String me) => Spec -> me ()
validateSpec s = do
    let ?spec = s
    -- First pass
    validateSpecNS
    mapM validateTmInstances   (specTemplate s)
    mapM validateTmPorts       (specTemplate s)
    mapM validateTmDerives     (specTemplate s)
    validateSpecDerives
    mapM validateTmNS          (specTemplate s)
    mapM (validateTypeSpec ScopeTop . tspec) (specType s)
    mapM (validateTmTypeDecls) (specTemplate s)
    validateTypeDeps
    mapM (validateConst ScopeTop) (specConst s)
    mapM validateTmConsts      (specTemplate s)
    mapM validateTmGVars       (specTemplate s)
    mapM validateTmContAssigns (specTemplate s)

    -- Second pass
    mapM validateTmMethods     (specTemplate s)
    return ()

-- Validating instance:
-- * only concrete templates can be instantiated
--
-- Checks that require CFG analysis
-- * All loops contain pause
-- * All exits from non-void methods end with a return statement
--
-- Checks to be performed on pre-processed spec
-- * variable visibility violations:
--   - variables automatically tainted as invisible because they are accessed from invisible context 
--     (process or invisible task) cannot be read inside uncontrollable visible transitions (which
--     correspond to executable driver code)
-- * No circular dependencies among ContAssign variables


-- Validate top-level namespace:
-- * No identifier is declared twice at the top level
validateSpecNS :: (?spec::Spec, MonadError String me) => me ()
validateSpecNS = 
    uniqNames (\n -> "Identifier " ++ n ++ " declared more than once in the top-level scope") specNamespace
