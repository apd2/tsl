{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Spec(Spec(Spec,specTemplate,specType,specConst), 
            emptySpec) where

import Data.List
import Data.Maybe
import Control.Monad.Error
import qualified Text.PrettyPrint as P

import PP
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

instance PP Spec where 
    pp (Spec tms ts cs) = (P.vcat $ map ((P.$+$ P.text "") . pp) ts)
                          P.$+$
                          (P.vcat $ map ((P.$+$ P.text "") . pp) cs)
                          P.$+$
                          (P.vcat $ map ((P.$+$ P.text "") . pp) tms)

emptySpec = Spec [] [] []
