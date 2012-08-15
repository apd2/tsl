{-# LANGUAGE ImplicitParams, UndecidableInstances #-}

module Const(Const(Const,constVal)) where

import Text.PrettyPrint

import PP
import Pos
import Name
import Expr
import TypeSpec

data Const = Const { cpos     :: Pos
                   , ctyp     :: TypeSpec
                   , cname    :: Ident
                   , constVal :: ConstExpr}

instance PP Const where
    pp (Const _ t n e) = text "const" <+> pp t <+> pp n <+> char '=' <+> pp e

instance WithPos Const where
    pos       = cpos
    atPos c p = c{cpos = p}

instance WithName Const where
    name = cname

instance WithType Const where
    typ = ctyp
