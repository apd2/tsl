{-# LANGUAGE ImplicitParams, UndecidableInstances #-}

module Var(Var(varInit)) where

import Pos
import Name
import TypeSpec
import Expr

data Var = Var { vpos    :: Pos
               , vname   :: Ident
               , vtyp    :: TypeSpec
               , varInit :: Maybe Expr}

instance WithPos Var where
    pos = vpos

instance WithName Var where
    name = vname

instance WithType Var where
    typ = vtyp
