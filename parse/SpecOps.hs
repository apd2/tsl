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
import TemplateValidate
import Const
import ConstOps
import Expr
import ExprOps

-- TODO:
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
-- * Validate call graph (no recursion, all possible stacks are valid (only invoke methods allowed in this context))
--   This cannot be done earlier because of method overrides
-- * XXX: re-validate method and process bodies to make sure that continuous assignment variables are not assigned


-----------------------------------------------------------------------------
-- Validation
-----------------------------------------------------------------------------

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
-- * Validate method declarations and implementation
-- * Validate template instances (only concrete templates can be instantiated, no circular instantiations)
-- * Validate processes
-- * Validate initial assignment expressions in constant declarations
-- * Validate array size declarations (must be integer constants)
-- * Validate initial variable assignments
-- * Validate RHS of continous assignments
-- * Validate goals
-- * Validate call graph

validateSpec :: (MonadError String me) => Spec -> me ()
validateSpec s = do
    let ?spec = s
    -- First pass
    validateSpecNS
    mapM validateTmInstances                  (specTemplate s)
    mapM validateTmPorts                      (specTemplate s)
    mapM validateTmDerives                    (specTemplate s)
    validateSpecDerives
    mapM validateTmNS                         (specTemplate s)
    mapM (validateTypeSpec ScopeTop . tspec)  (specType s)
    mapM validateTmTypeDecls                  (specTemplate s)
    validateTypeDeps
    mapM (validateConst ScopeTop)             (specConst s)
    mapM validateTmConsts                     (specTemplate s)
    mapM validateTmGVars                      (specTemplate s)
    mapM validateTmWires                      (specTemplate s)

    -- Second pass
    mapM validateTmInit2                      (specTemplate s)
    mapM validateTmMethods2                   (specTemplate s)
    mapM validateTmInstances2                 (specTemplate s)
    validateSpecInstances2
    mapM validateTmProcesses2                 (specTemplate s)
    mapM (validateConst2 ScopeTop)            (specConst s)
    mapM validateTmConsts2                    (specTemplate s)
    mapM validateTmGVars2                     (specTemplate s)
    mapM (validateTypeSpec2 ScopeTop . tspec) (specType s)
    mapM validateTmTypeDecls2                 (specTemplate s)
    mapM validateTmWires2                     (specTemplate s)
    mapM validateTmGoals2                     (specTemplate s)
    validateSpecCallGraph2

    return ()

-- Validate top-level namespace:
-- * No identifier is declared twice at the top level
validateSpecNS :: (?spec::Spec, MonadError String me) => me ()
validateSpecNS = 
    uniqNames (\n -> "Identifier " ++ n ++ " declared more than once in the top-level scope") specNamespace

-- Validate the derivation graph of a spec
-- * no circular derivations
validateSpecDerives :: (?spec::Spec, MonadError String me) => me ()
validateSpecDerives = 
    case grCycle $ fst drvGraph of
         Nothing -> return ()
         Just c  -> err (pos $ snd $ head c) $ "Template derivation cycle: " ++ (intercalate "->" $ map (show . snd) c) 

-- Validate the instantiation graph of a spec
-- * no circular derivations
validateSpecInstances2 :: (?spec::Spec, MonadError String me) => me ()
validateSpecInstances2 = case grCycle instGraph of
                              Nothing -> return ()
                              Just c  -> err (pos $ snd $ head c) $ "Template instantiation cycle: " ++ (intercalate "->" $ map (show . snd) c) 

-- Validate the callgraph of the spec
-- * no recursion
validateSpecCallGraph2 :: (?spec::Spec, MonadError String me) => me ()
validateSpecCallGraph2 = 
    case grCycle callGraph of
         Nothing -> return ()
         Just c  -> err p $ "Recursive method invocation: " ++ 
                            (intercalate "->" $ map (\(_, s) -> 
                                   case s of
                                        ScopeMethod  t m -> sname t ++ "::" ++ sname m
                                        ScopeProcess t p -> sname t ++ "::" ++ sname p) c)
                    where p = case snd $ head c of
                                   ScopeMethod _ m  -> pos m
                                   ScopeProcess _ p -> pos p

-- Map function overl all expressions in the spec
specMapExpr :: (Scope -> Expr -> Expr) -> Spec -> Spec
specMapExpr f s =
    let ?spec = s
    in let tm' = map (tmMapExpr f) (specTemplate s)
           t'  = map (\t -> TypeDecl (pos t) (tspecMapExpr f ScopeTop $ tspec t) (name t)) (specType s)
           c'  = map (\c -> c{constVal = mapExpr f ScopeTop (constVal c)}) (specConst s)
       in Spec tm' t' c'

---------------------------------------------------------------------
-- Flattening
---------------------------------------------------------------------

-- Flatten static enum or const name by prepending template name to it
flattenName :: (WithName a) => Template -> a -> Ident
flattenName t x = Ident (pos $ name x) $ (sname t) ++ "::" ++ (sname x)


-- Move constants from templates to the top level
flattenConsts :: Spec -> Spec
flattenConsts s = s''{specTemplate = map (\t -> t{tmConst = []}) (specTemplate s'')}
    where s'  = let ?spec = s 
                in specMapExpr exprFlattenConsts s
          s'' = foldl' (\s t -> foldl' (\s c -> flattenConst s t c) s (tmConst t)) s' (specTemplate s')
                                   
flattenConst :: Spec -> Template -> Const -> Spec
flattenConst s t c = s{specConst = c':(specConst s)}
    where c' = Const (pos c) (tspec c) (flattenName t c) (constVal c)

exprFlattenConsts :: (?spec::Spec) => Scope -> Expr -> Expr
exprFlattenConsts s e = case e of
                             ETerm p sym  -> case getTerm s sym of
                                                  ObjConst (ScopeTemplate t) c -> ETerm p [flattenName t c]
                                                  _             -> e
                             _            -> e


-- Move enums from templates to the top level
flattenEnums :: Spec -> Spec
flattenEnums s = s''{specTemplate = map (\t -> t{tmConst = []}) (specTemplate s'')}
    where s'  = let ?spec = s 
                in specMapExpr exprFlattenEnums s
          s'' = foldl' (\s t -> foldl' (\s d -> flattenEnumDecl s t d) s (tmTypeDecl t)) s' (specTemplate s')
                                   
flattenEnumDecl :: Spec -> Template -> TypeDecl -> Spec
flattenEnumDecl s t d = case tspec d of
                         sp@(EnumSpec p es) -> let d' = TypeDecl (pos d) (flattenEnumSpec t sp) (flattenName t d)
                                               in s{specType = d':(specType s)}
                         _                  -> s
        
flattenEnumSpec :: Template -> TypeSpec -> TypeSpec
flattenEnumSpec t (EnumSpec p es) = EnumSpec p (map (\e -> Enumerator (pos e) (flattenName t e)) es)

exprFlattenEnums :: (?spec::Spec) => Scope -> Expr -> Expr
exprFlattenEnums s e = case e of
                             ETerm p sym  -> case getTerm s sym of
                                                  ObjEnum (Type (ScopeTemplate t) _) en -> ETerm p [flattenName t en]
                                                  _                                     -> e
                             _            -> e

