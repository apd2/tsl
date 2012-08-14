module Const(Const) where

import Pos
import Name
import Type
import qualified Expr     as E
import qualified TypeSpec as T

data Const = Const { cpos   :: Pos
                   , ctyp   :: T.TypeSpec
                   , cname  :: Ident
                   , val    :: E.ConstExpr}

instance WithPos Const where
    pos = cpos

instance WithName Const where
    name = cname

instance WithType Const where
    typ = typ . ctyp
