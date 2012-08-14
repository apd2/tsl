module Spec(Spec, getTemplate) where

import qualified TypeSpec as T
import qualified Template as Tm
import qualified Const    as C

data Spec { template :: [Tm.Template]
          , typedecl :: [T.TypeDecl]
          , const    :: [C.Const]}

getTemplate :: Ident -> Tm.Template

instance StaticNS Spec Obj where
    slookup s i = listToMaybe [t,c,e]
        where -- search for the name in the local scope
              t = fmap ObjTemplate $ find ((== n) . name) (template s)
              c = fmap ObjConst    $ find ((== n) . name) (const t)
              e = listToMaybe $ map (\t -> slookup t i) (typedecl s)
