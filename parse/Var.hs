{-# LANGUAGE ImplicitParams, UndecidableInstances #-}

module Var(Var(Var,varInit)) where

import Text.PrettyPrint

import Pos
import Name
import PP
import TypeSpec
import Expr

data Var = Var { vpos      :: Pos
               , vtyp      :: TypeSpec
               , vname     :: Ident
               , varInit   :: Maybe Expr}

instance PP Var where
    pp (Var _ t n Nothing)  = pp t <+> pp n
    pp (Var _ t n (Just i)) = pp t <+> pp n <+> char '=' <+> pp i

instance WithPos Var where
    pos       = vpos
    atPos v p = v{vpos = p}

instance WithName Var where
    name = vname

instance WithTypeSpec Var where
    tspec = vtyp
