{-# LANGUAGE ImplicitParams, TupleSections, FlexibleContexts #-}

module Ctx(Ctx(..),
           ctxLookupType,
           ctxCheckType,
           ctxGetType,
           ctxGTypeName,
           ctxUniqName) where

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

data Ctx = CtxTop
         | CtxTemplate {ctxTm::Template}
         | CtxMethod   {ctxTm::Template, ctxMeth::Method}

ctxLookupTypeLocal :: (?spec::Spec) => Ctx -> Ident -> Maybe TypeDecl
ctxLookupTypeLocal CtxTop          n = find ((==n) . name) (specType ?spec)
ctxLookupTypeLocal (CtxTemplate t) n = find ((==n) . name) (tmTypeDecl t)

ctxLookupType :: (?spec::Spec) => Ctx -> StaticSym -> Maybe (TypeDecl,Ctx)
ctxLookupType CtxTop [n]            = fmap (,CtxTop) $ ctxLookupTypeLocal CtxTop n
ctxLookupType CtxTop sn@(n:[n'])    = case specLookupTemplate n of
                                           Nothing -> Nothing
                                           Just t  -> fmap (,CtxTemplate t) $ ctxLookupTypeLocal (CtxTemplate t) n'
ctxLookupType c@(CtxTemplate t) [n] = case ctxLookupTypeLocal c n of
                                           Nothing -> fmap (,CtxTop) $ ctxLookupTypeLocal CtxTop n
                                           Just t  -> Just (t, c)
ctxLookupType (CtxMethod t _) ns    = ctxLookupType (CtxTemplate t) ns
ctxLookupType _               _     = Nothing

ctxCheckType  :: (?spec::Spec, MonadError String me ) => Ctx -> StaticSym -> me ()
ctxCheckType c n = do
    case ctxLookupType c n of
       Nothing -> err (pos n) $ "Unknown type: " ++ (show n)
       Just t -> return ()


ctxGetType :: (?spec::Spec) => Ctx -> StaticSym -> (TypeDecl,Ctx)
ctxGetType c = fromJustMsg "ctxGetType: type not found" . ctxLookupType c

ctxGTypeName :: (TypeDecl,Ctx) -> GStaticSym
ctxGTypeName (d,CtxTop)        = [name d]
ctxGTypeName (d,CtxTemplate t) = [name t,name d]

ctxUniqName :: (?spec::Spec, MonadError String me) => Ctx -> Ident -> me ()
ctxUniqName = undefined
