{-# LANGUAGE ImplicitParams, TupleSections, FlexibleContexts #-}

module Scope(Scope(..),
             scopeLookupType, scopeCheckType, scopeGetType,
             scopeGTypeName,
             scopeUniqName,
             scopeLookupTerm, scopeCheckTerm, scopeGetTerm) where

import Control.Monad.Error
import Data.List
import Data.Maybe

import Util hiding (name)
import Pos
import TSLUtil
import Name
import TypeSpec
import Template
import Method
import Process
import Spec
import SpecOps
import NS

data Scope = ScopeTop
           | ScopeTemplate {scopeTm::Template}
           | ScopeMethod   {scopeTm::Template, scopeMeth::Method}
           | ScopeProcess  {scopeTm::Template, scopeProc::Process}

-- Type lookup

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
scopeLookupType (ScopeProcess t _) ns   = scopeLookupType (ScopeTemplate t) ns
scopeLookupType _                 _     = Nothing

scopeCheckType  :: (?spec::Spec, MonadError String me ) => Scope -> StaticSym -> me (TypeDecl,Scope)
scopeCheckType c n = do
    case scopeLookupType c n of
       Nothing -> err (pos n) $ "Unknown type: " ++ (show n)
       Just t -> return t


scopeGetType :: (?spec::Spec) => Scope -> StaticSym -> (TypeDecl,Scope)
scopeGetType c = fromJustMsg "scopeGetType: type not found" . scopeLookupType c

scopeGTypeName :: (TypeDecl,Scope) -> GStaticSym
scopeGTypeName (d,ScopeTop)        = [name d]
scopeGTypeName (d,ScopeTemplate t) = [name t,name d]

-- Term lookup
-- A term is either a local name, which corresponds to any object in the local or
-- containing scope, or a global name (more than one ::-separate identifiers), which
-- must refer to a constant or enum name.
scopeLookupTerm :: (?spec::Spec) => Scope -> StaticSym -> Maybe (Obj,Scope)

scopeLookupTerm s@ScopeTop          [n] = fmap (,s) $ specLookup n
scopeLookupTerm s@(ScopeTemplate t) [n] = listToMaybe $ catMaybes [tm,global]
    where tm     = fmap (,s) $ objLookup (ObjTemplate t) n
          global = scopeLookupTerm ScopeTop [n]
scopeLookupTerm s@(ScopeMethod t m) [n] = listToMaybe $ catMaybes [local,tm,global]
    where local  = fmap (,s)               $ objLookup (ObjMethod m) n
          tm     = fmap (,ScopeTemplate t) $ objLookup (ObjTemplate t) n
          global = scopeLookupTerm ScopeTop [n]
scopeLookupTerm s@(ScopeProcess t p) [n] = listToMaybe $ catMaybes [local,tm,global]
    where local  = fmap (,s)               $ objLookup (ObjProcess p) n
          tm     = fmap (,ScopeTemplate t) $ objLookup (ObjTemplate t) n
          global = scopeLookupTerm ScopeTop [n]

scopeLookupTerm _ [tn,n] = 
    case specLookupTemplate tn of
         Nothing -> Nothing
         Just t  -> case objLookup (ObjTemplate t) n of
                         Nothing             -> Nothing
                         Just o@(ObjConst _) -> Just (o, ScopeTemplate t)
                         Just o@(ObjEnum  _) -> Just (o, ScopeTemplate t)
                         _                   -> Nothing

scopeCheckTerm :: (?spec::Spec, MonadError String me) => Scope -> StaticSym -> me (Obj,Scope)
scopeCheckTerm s n = case scopeLookupTerm s n of 
                        Nothing -> err (pos n) $ "Unknown term " ++ show n
                        Just t  -> return t

scopeGetTerm :: (?spec::Spec) => Scope -> StaticSym -> (Obj,Scope)
scopeGetTerm s n = fromJustMsg "scopeGetTerm: term lookup failed" $ scopeLookupTerm s n 

scopeUniqName :: (?spec::Spec, MonadError String me) => Scope -> Ident -> me ()
scopeUniqName = undefined
