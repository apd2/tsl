{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Spec(Spec(specTemplate), 
            emptySpec,
            specAddTemplate,
            specAddConst,
            specAddType,
            specLookupTemplate, specGetTemplate, specCheckTemplate,
            Ctx(), 
            ctxCheckType, ctxGetType, ctxLookupType,
            ctxUniqName) where

import Data.List
import Data.Maybe
import Control.Monad.Error

import TSLUtil
import Util hiding (name)
import Name
import Pos
import TypeSpec
import Template
import Const
import Method

-- Validation order
-- * Validate instances (required by derive statements)
-- * Validate derive statements (required to build template namespaces)
-- * Validate types
-- * Validate constants

-- Validating type declaration:
-- * no cyclic dependencies among types
--
-- Validating instance:
-- * only concrete templates can be instantiated
--
-- Additionally for enum declarations
-- * enum values must be valid static expressions
--
-- Validating template declarations:
-- * ports refer to valid template names
-- * variables, goals, continuous assignments do not override existing parent declarations
-- * method declarations match prototypes in parent templates
-- * ports, variables, goals, processes, methods, types have unique names
-- 
-- Validating constant declarations
-- * names must be unique in the template or global scope
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
-- Validating expressions
-- * terms refer to variables that are 
--   - visible in the current scope;
--   - are not continuous assignment variables
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
-- * assign: LHS is a valid l-value expression; RHS is a valid expression of a matching type
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

data Spec = Spec { specTemplate :: [Template]
                 , specType     :: [TypeDecl]
                 , specConst    :: [Const]}

emptySpec = Spec [] [] []

specLookupTemplate :: (?spec::Spec) => Ident -> Maybe Template
specLookupTemplate n = find ((==n) . name) (specTemplate ?spec)

specGetTemplate :: (?spec::Spec) => Ident -> Template
specGetTemplate n = fromJustMsg ("getTemplate failed: " ++ show n) $ specLookupTemplate n

specCheckTemplate :: (?spec::Spec, MonadError String me) => Ident -> me ()
specCheckTemplate n = do
    case specLookupTemplate n of
       Nothing -> err (pos n) $ "Invalid template name: " ++ (show $ pos n)
       Just t -> return ()

specLookup :: Spec -> Ident -> Maybe Pos
specLookup s n = listToMaybe $ catMaybes [tm, t, c]
    where tm = fmap pos $ find ((== n) . name) (specTemplate s)
          t  = fmap pos $ find ((== n) . name) (specType s)
          c  = fmap pos $ find ((== n) . name) (specConst s)

specCheckName :: (MonadError String me) => Spec -> Ident -> me ()
specCheckName s n = do
    case specLookup s n of
         Just p -> err (pos n) $ "Duplicate declaration: " ++ "identifier " ++ show n ++ " already defined at " ++ show p
         Nothing -> return ()

specAddTemplate :: (MonadError String me) => Spec -> Template -> me Spec
specAddTemplate s t = do
    specCheckName s (name t)
    return $ s{specTemplate = t:(specTemplate s)}

specAddType :: (MonadError String me) => Spec -> TypeDecl -> me Spec
specAddType s t = do
    specCheckName s (name t)
    return $ s{specType = t:(specType s)}

specAddConst :: (MonadError String me) => Spec -> Const -> me Spec
specAddConst s c = do
    specCheckName s (name c)
    return $ s{specConst = c:(specConst s)}


data Ctx = CtxTop
         | CtxTemplate {ctxTm::Template}
         | CtxMethod   {ctxTm::Template, ctxMeth::Method}

ctxLookupTypeLocal :: (?spec::Spec) => Ctx -> Ident -> Maybe TypeDecl
ctxLookupTypeLocal CtxTop          n = find ((==n) . name) (specType ?spec)
ctxLookupTypeLocal (CtxTemplate t) n = find ((==n) . name) (tmTypeDecl t)

ctxLookupType :: (?spec::Spec) => Ctx -> StaticSym -> Maybe TypeDecl
ctxLookupType CtxTop [n]            = ctxLookupTypeLocal CtxTop n
ctxLookupType CtxTop (n:[n'])         = case specLookupTemplate n of
                                           Nothing -> Nothing
                                           Just t  -> ctxLookupTypeLocal (CtxTemplate t) n'
ctxLookupType c@(CtxTemplate t) [n] = case ctxLookupTypeLocal c n of
                                           Nothing -> ctxLookupTypeLocal CtxTop n
                                           Just t  -> Just t
ctxLookupType (CtxMethod t _) ns    = ctxLookupType (CtxTemplate t) ns
ctxLookupType _               _     = Nothing

ctxCheckType  :: (?spec::Spec) => Ctx -> StaticSym -> Bool
ctxCheckType c = isJust . ctxLookupType c

ctxGetType :: (?spec::Spec) => Ctx -> StaticSym -> TypeDecl
ctxGetType c = fromJustMsg "ctxGetType: type not found" . ctxLookupType c

ctxUniqName :: (?spec::Spec, MonadError String me) => Ctx -> Ident -> me ()
ctxUniqName = undefined


----------------------------------------------------
-- Resolve syntax tree
----------------------------------------------------
--
--resolve :: (MonadError String me) => [(FilePath, ST.Spec)] -> me Spec
--resolve sts = do
--    -- Fill out the spec without resolving references first
--    spec <- foldM scanFile emptySpec sts
--          -- templates, ports, derivation, instances.  Check consistency.
--          -- types. Check consistency.
--          -- enums.
--          -- constants.  Resolve constant expressions.
--          -- variables.  Resolve assignment expressions.
--          -- methods.
--
--scanSpecItem f p spec (ST.SpType tdef) = do
--    tdecl <- scanTypeDef f p tdef
--    case find ((== name tdecl) . name) (typedecl spec) of
--         Nothing -> return $ spec {typedecl = tdecl:(typedecl spec)}
--         Just t  -> err (f,p) $ "Duplicate type name " ++ name tdecl ++ ".  Previous declaration: " ++ show (pos t)
