{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Spec(Spec(Spec,specTemplate,specType,specConst), 
            emptySpec) where

import Data.List
import Data.Maybe
import Control.Monad.Error

import TSLUtil
import Util hiding (name)
import Name
import Pos
import Type
import Template
import Const
import Method

data Spec = Spec { specTemplate :: [Template]
                 , specType     :: [TypeDecl]
                 , specConst    :: [Const]}

emptySpec = Spec [] [] []
