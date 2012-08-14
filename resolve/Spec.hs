module Spec(Spec, lookupTemplate) where

import Data.List

import Name
import qualified TypeSpec as T
import qualified Template as Tm
import qualified Const    as C

data Spec = Spec { template :: [Tm.Template]
                 , typedecl :: [T.TypeDecl]
                 , const    :: [C.Const]}

lookupTemplate :: Spec -> Ident -> Maybe Tm.Template
lookupTemplate s n = find ((==n) . name) (template s)
