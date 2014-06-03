module Internal.IVar(VarCategory(..),
            Var(..)) where

import Text.PrettyPrint

import PP
import Internal.IType

data VarCategory = VarState
                 | VarTmp
                 deriving (Eq, Ord, Show)

data Var = Var { varMem  :: Bool
               , varCat  :: VarCategory
               , varName :: String
               , varType :: Type
               }

instance Eq Var where
    (==) v1 v2 = varName v1 == varName v2

instance Ord Var where
    compare v1 v2 = compare (varName v1) (varName v2)

instance PP Var where
    pp (Var mem cat n t) = (text $ if cat == VarTmp then "temp" else "state") <+> (if mem then text "mem" else empty) <+> pp t <+> text n

instance Show Var where
    show = render . pp

instance Typed Var where
    typ = varType
