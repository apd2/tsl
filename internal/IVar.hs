module IVar(VarCategory(..),
            Var(..)) where

import Text.PrettyPrint

import PP
import IType
import PredicateDB

data Var = Var { varMem  :: Bool
               , varCat  :: VarCategory
               , varName :: String
               , varType :: Type
               }

instance PP Var where
    pp (Var mem cat n t) = (text $ if cat == VarTmp then "temp" else "state") <+> (if mem then text "mem" else empty) <+> pp t <+> text n

instance Typed Var where
    typ = varType
