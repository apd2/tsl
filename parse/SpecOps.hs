{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module SpecOps(specNamespace) where

import Data.List
import Data.Maybe
import Control.Monad.Error

import TSLUtil
import TypeSpec
import Pos
import Name
import Spec
import NS
import Template
import Const

-- Validation order:
--
-- * Validate top-level namespace
-- * Validate template instances (required by derive statements)
-- * Validate template ports (required by derive statements)
-- * Validate derive statements (required to build template namespaces)
-- * Validate template namespaces
-- * Validate types (but not array sizes)
-- * Validate constant types (but not initial assignments)
-- * Validate variable types (but not initial assignments)
-- * Validate continuous assignments (LHS only)
-- We are now ready to validate components of the specification containing expressions:
-- * Validate method declarations
-- * Validate call graph (no recursion, all possible stacks are valid (only invoke methods allowed in this context))
-- * Validate process declarations
-- * Validate initial assignment expressions in constant declarations
-- * Validate array size declarations (must be constant)
-- * Validate initial variable assignments
-- * Validate process and method bodies
-- * Validate RHS of continous assignments; check acyclicity of cont assignments
-- From now on, check that

-- Validating instance:
-- * only concrete templates can be instantiated
--
-- Additionally for enum declarations
-- * enum values must be valid static expressions
--
-- Validating constant declarations
-- * value expressions are valid and type-compliant static expressions
-- 
-- Validating variable declarations
-- * name must be unique in the current scope
-- * valid type spec
-- * type cannot be void
-- * initial assignment must be a valid expression of a matching type
--
-- Validating method declarations
-- * valid argument and return types
-- * argument types cannot be void
--
-- Validate process declarations:
-- * var declarations have unique names
--
-- 
-- Validating goals:
-- 
--
-- Validating continuous assignments:
-- * LHS must be a variable, field or slice (no pointers, array elements)
-- * LHS's must not overlap
-- * a variable must be assigned in full (all of its bits)
-- * no circular dependencies between continuous assignments

-- Checks to be performed on pre-processed spec
-- * variable visibility violations:
--   - variables automatically tainted as invisible because they are accessed from invisible context 
--     (process or invisible task) cannot be read inside uncontrollable visible transitions (which
--     correspond to executable driver code)


specNamespace :: (?spec::Spec) => [Obj]
specNamespace = map ObjTemplate (specTemplate ?spec) ++ 
                map (ObjTypeDecl ScopeTop) (specType ?spec) ++ 
                map (ObjConst    ScopeTop) (specConst ?spec) ++ 
                (concat $ map (\d -> case tspec d of
                                          EnumSpec _ es -> map (ObjEnum (Type ScopeTop $ tspec d)) es
                                          _             -> []) (specType ?spec))

-- Validate top-level namespace:
-- * No identifier is declared twice at the top level
validateSpecNS :: (?spec::Spec, MonadError String me) => me ()
validateSpecNS = 
    uniqNames (\n -> "Identifier " ++ n ++ " declared more than once in the top-level scope") specNamespace
