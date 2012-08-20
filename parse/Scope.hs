{-# LANGUAGE ImplicitParams, TupleSections, FlexibleContexts #-}

module Scope(Scope(..),
             scopeLookupType,
             scopeCheckType,
             scopeGetType,
             scopeGTypeName,
             scopeUniqName) where

import Util hiding (name)
import Control.Monad.Error
import Data.List

import Pos
import TSLUtil
import Name
import TypeSpec
import Template
import Method
import Spec

data Scope = ScopeTop
           | ScopeTemplate {scopeTm::Template}
           | ScopeMethod   {scopeTm::Template, scopeMeth::Method}

scopeLookupTypeLocal :: (?spec::Spec) => Scope -> Ident -> Maybe TypeDecl
scopeLookupTypeLocal ScopeTop          n = find ((==n) . name) (specType ?spec)
scopeLookupTypeLocal (ScopeTemplate t) n = find ((==n) . name) (tmTypeDecl t)

scopeLookupType :: (?spec::Spec) => Scope -> StaticSym -> Maybe (TypeDecl,Scope)
scopeLookupType ScopeTop [n]            = fmap (,ScopeTop) $ scopeLookupTypeLocal ScopeTop n
scopeLookupType ScopeTop sn@(n:[n'])    = case specLookupTemplate n of
                                               Nothing -> Nothing
                                               Just t  -> fmap (,ScopeTemplate t) $ scopeLookupTypeLocal (ScopeTemplate t) n'
scopeLookupType c@(ScopeTemplate t) [n] = case scopeLookupTypeLocal c n of
                                               Nothing -> fmap (,ScopeTop) $ scopeLookupTypeLocal ScopeTop n
                                               Just t  -> Just (t, c)
scopeLookupType (ScopeMethod t _) ns    = scopeLookupType (ScopeTemplate t) ns
scopeLookupType _                 _     = Nothing

scopeCheckType  :: (?spec::Spec, MonadError String me ) => Scope -> StaticSym -> me ()
scopeCheckType c n = do
    case scopeLookupType c n of
       Nothing -> err (pos n) $ "Unknown type: " ++ (show n)
       Just t -> return ()


scopeGetType :: (?spec::Spec) => Scope -> StaticSym -> (TypeDecl,Scope)
scopeGetType c = fromJustMsg "scopeGetType: type not found" . scopeLookupType c

scopeGTypeName :: (TypeDecl,Scope) -> GStaticSym
scopeGTypeName (d,ScopeTop)        = [name d]
scopeGTypeName (d,ScopeTemplate t) = [name t,name d]

scopeUniqName :: (?spec::Spec, MonadError String me) => Scope -> Ident -> me ()
scopeUniqName = undefined
