{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Spec(Spec(Spec,specTemplate,specType,specConst), 
            emptySpec,
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

specCheckTemplate :: (?spec::Spec, MonadError String me) => Ident -> me (Template)
specCheckTemplate n = do
    case specLookupTemplate n of
       Nothing -> err (pos n) $ "Unknown template name: " ++ (show n)
       Just t -> return t
