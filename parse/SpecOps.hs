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

--specLookup :: (?spec::Spec) => Ident -> Maybe Obj
--specLookup n = listToMaybe $ catMaybes [tm, t, c]
--    where tm = fmap (ObjTemplate ScopeTop) $ find ((== n) . name) (specTemplate ?spec)
--          t  = fmap (ObjTypeDecl ScopeTop) $ find ((== n) . name) (specType ?spec)
--          c  = fmap (ObjConst    ScopeTop) $ find ((== n) . name) (specConst ?spec)

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
-- * Validate array size declarations
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
-- Validating expressions
-- * terms refer to variables that are 
--   - visible in the current scope;
-- * literals: value matches width
-- * method applications:
--   - method name refers to a visible method (local or exported)
--   - if the method is a task, then the current context must be a process or task
--   - the number and types of arguments match
--   - no recursion
-- * field selection refers to a valid field or variable name in a template
-- * index[]: applied to an array type expression; index value is a valid 
--   integral expression 
-- * unary/binary/ternary operators are applied to expressions of matching types
-- * case: 
--    - all components are valid expressions
--    - case conditions must type-match the case expression (should they be statically computable?)
--    - value expressions must match the type of the key expression
-- * cond: 
--    - condition expressions are valid boolean expressions
--    - value expressions have compatible types
-- * slice: 
--    - applied to an integer (unsigned?) value; 
--    - lower and upper bounds are constant expressions
--    - 0 <= lower bound <= upper bound <= type width - 1
-- * struct:
--    - typename refers to a struct type
--    - correct number and types of fields
--
-- Validating statements
-- * SVarDecl {spos::Pos, svar::Var}
-- * return: value expression has correct type
-- * all loops
--   - there is no path through the loop body that does not break out of the loop and
--     does not contain some form of pause
-- * do, while, for loops: loop condition must be a valid boolean expression
-- * pause - only allowed inside an uncontrollable or invisible task or a process
-- * stop - only allowed inside an uncontrollable or invisible task or a process
-- * break - only allowed inside a loop
-- * method invocations
--   - method name refers to a visible method (local or exported)
--   - if the method is a task, then the current context must be a process or task
--   - the number and types of arguments match
--   - no recursion
-- * assert, assume arguments must be valid, side effect-free boolean expressions 
-- * assign: LHS is a valid l-value expression (in particular, it cannot be a continous 
--   assignment variable); RHS is a valid expression of a matching type
-- * if-then-else.  The conditional expression is of type bool
-- * case: the key expression and case clauses have matching types
-- * magic block: 
--   - only allowed in uncontrollable tasks (and processes?)
--   - valid goal name or boolean goal expression
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
specNamespace = map (ObjTemplate ScopeTop) (specTemplate ?spec) ++ 
                map (ObjTypeDecl ScopeTop) (specType ?spec) ++ 
                map (ObjConst    ScopeTop) (specConst ?spec) ++ 
                (concat $ map (\t -> case typ t of
                                          EnumSpec _ es -> map (ObjEnum ScopeTop) es
                                          _             -> []) (specType ?spec))

-- Validate top-level namespace:
-- * No identifier is declared twice at the top level
validateSpecNS :: (?spec::Spec, MonadError String me) => me ()
validateSpecNS = 
    uniqNames (\n -> "Identifier " ++ n ++ " declared more than once in the top-level scope") specNamespace
