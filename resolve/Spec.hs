{-# LANGUAGE ImplicitParams #-}

module Spec(Spec, 
            lookupTemplate, 
            getTemplate) where

import Data.List

import Util hiding (name)
import Name
import TypeSpec
import Template
import Const

data Spec = Spec { template :: [Template]
                 , typedecl :: [TypeDecl]
                 , const    :: [Const]}

lookupTemplate :: (?spec::Spec) => Ident -> Maybe Template
lookupTemplate n = find ((==n) . name) (template ?spec)

getTemplate :: (?spec::Spec) => Ident -> Template
getTemplate n = fromJustMsg ("getTemplate failed: " ++ show n) $ lookupTemplate n

