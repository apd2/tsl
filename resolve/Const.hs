{-# LANGUAGE ImplicitParams, UndecidableInstances #-}

module Const(Const(constVal)) where

import Pos
import Name
import Expr
import TypeSpec

data Const = Const { cpos     :: Pos
                   , ctyp     :: TypeSpec
                   , cname    :: Ident
                   , constVal :: ConstExpr}

instance WithPos Const where
    pos = cpos

instance WithName Const where
    name = cname

instance WithType Const where
    typ = ctyp
