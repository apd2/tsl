{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Spec(Spec(specTemplate,specType,specConst), 
            emptySpec,
            specAddTemplate,
            specAddConst,
            specAddType,
            specLookupTemplate, specGetTemplate, specCheckTemplate) where

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
       Nothing -> err (pos n) $ "Unknown template name: " ++ (show n)
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
