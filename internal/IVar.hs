module IVar(VarCategory(..),
            Var(..)) where

import IType
import AbsGame

data Var = Var { varMem  :: Bool
               , varCat  :: VarCategory
               , varName :: String
               , varType :: Type
               }

instance Typed Var where
    typ = varType
