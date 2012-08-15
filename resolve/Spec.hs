{-# LANGUAGE ImplicitParams #-}

module Spec(Spec, 
            lookupTemplate, 
            getTemplate) where

import Data.List
import Control.Monad.Error

import Util hiding (name)
import Name
import TypeSpec
import Template
import Const

data Spec = Spec { template :: [Template]
                 , typedecl :: [TypeDecl]
                 , const    :: [Const]}

specLookupTemplate :: (?spec::Spec) => Ident -> Maybe Template
specLookupTemplate n = find ((==n) . name) (template ?spec)

specGetTemplate :: (?spec::Spec) => Ident -> Template
specGetTemplate n = fromJustMsg ("getTemplate failed: " ++ show n) $ lookupTemplate n

specCheckName :: (MonadError String me) => Spec -> Ident -> me ()
specCheckName s n = do
    case specLookup s n of
         Just p -> err (pos n) $ "Duplicate declaration: " ++ "identifier " ++ (name t) ++ " already defined at " ++ show p
         Nothing -> return ()

specAddTemplate :: (MonadError String me) => Spec -> Template -> me Spec
specAddTemplate s t = do
    specCheckName s (name t)
    return $ s{template = t:(template s)}

specAddType :: (MonadError String me) => Spec -> TypeDecl -> me Spec
specAddType s t = do
    specCheckName s (name t)
    return $ s{typedecl = t:(typedecl s)}

specAddConst :: (MonadError String me) => Spec -> Const -> me Spec
specAddConst s c = do
    specCheckName s (name c)
    return $ s{const = c:(const s)}

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
