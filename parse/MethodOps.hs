{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module MethodOps() where

import Data.Maybe
import Control.Monad.Error

import TSLUtil
import Pos
import Name
import NS
import Scope
import TypeSpec
import TypeSpecOps
import Method
import Template
import TemplateOps
import Spec

-- Objects declared in the method scope (arguments and local variables)
methLocalDecls :: (?spec::Spec) => Method -> [Obj]
methLocalDecls m = map ObjArg (methArg m) ++ map ObjVar (methVar m)

-- Local names are unique and do not override template-level names
validateMethNS :: (?spec::Spec, MonadError String me) => Template -> Method -> me ()
validateMethNS t m = do
    uniqNames (\n -> "Identifier " ++ n ++ " declared multiple times in method " ++ sname m) 
              (methLocalDecls m)
    
-- Check if the method overrides a derived declaration and, if so, 
-- make sure that method category, the number and types of arguments, 
-- and return types match
methCheckOverride :: (?spec::Spec, MonadError String me) => Template -> Method -> me ()
methCheckOverride t m = do
   case listToMaybe $ catMaybes $ map (\t' -> objLookup (ObjTemplate t') (name m)) (tmParents t) of
        Nothing             -> do mapM (validateTypeSpec (ScopeTemplate t) . typ) (methArg m)
                                  return ()
        Just (ObjMethod m') -> do
            assert (methCat m' == methCat m) (pos m) $ 
                   "Method " ++ sname m ++ " was declared as " ++ (show $ methCat m') ++ " at " ++ spos m' ++
                   " but is redefined as " ++ (show $ methCat m) ++ " at " ++ spos m
            assert (eqMType (methRettyp m', ScopeTemplate t) (methRettyp m, ScopeTemplate t)) (pos m) $ 
                   "Method " ++ sname m ++ " was declared with return type " ++ (show $ methRettyp m') ++ " at " ++ spos m' ++
                   " but is redefined as " ++ (show $ methRettyp m) ++ " at " ++ spos m
            assert ((length $ methArg m') == (length $ methArg m)) (pos m) $ 
                   "Method " ++ sname m ++ " was declared with " ++ (show $ length $ methArg m') ++ " arguments at " ++ spos m' ++
                   " but is redefined with " ++ (show $ length $ methArg m) ++ " arguments at " ++ spos m
            mapM (\((a1,a2),id) -> do assert (name a1 == name a2) (pos a2) $ 
                                             "Argument " ++ show id ++ " of method " ++ sname m ++ " was declared with name " ++ sname a1 ++ " at " ++ spos a1 ++
                                             " but is redefined as " ++ sname a2 ++ " at " ++ spos a2
                                      assert (argDir a1 == argDir a2 && (eqType (typ a1, ScopeTemplate t) (typ a2, ScopeTemplate t))) (pos a1) $ 
                                             "Argument " ++ sname a1 ++ " was declared as " ++ show (argDir a1) ++ " " ++ show (typ a1) ++ " at " ++ spos a1 ++
                                             " but is redefined as " ++ show (argDir a2) ++ " " ++ show (typ a2) ++ " at " ++ spos a2)
                 (zip (zip (methArg m') (methArg m)) [1..])
            return ()



validateMeth :: (?spec::Spec, MonadError String me) => Template -> Method -> me ()
validateMeth t m = do
    methCheckOverride t m
    validateMethNS t m
