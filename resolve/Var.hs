{-# LANGUAGE ImplicitParams, UndecidableInstances #-}

module Var(Var) where

import Pos
import Name
import qualified TypeSpec as T
import qualified Expr as E

data Var = Var { vpos  :: Pos
               , vname :: Ident
               , vtyp  :: T.TypeSpec
               , init  :: Maybe E.Expr}

instance WithPos Var where
    pos = vpos

instance WithName Var where
    name = vname

instance T.WithType Var where
    typ = vtyp
