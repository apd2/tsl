{-# LANGUAGE ImplicitParams, UndecidableInstances #-}

module TVar(Var(Var,varMem,varInit,varType,varName)) where

import Text.PrettyPrint

import Pos
import Name
import PP
import Type
import Expr

data Var = Var { vpos      :: Pos
               , varMem    :: Bool
               , varType   :: TypeSpec
               , varName   :: Ident
               , varInit   :: Maybe Expr}

instance PP Var where
    pp (Var _ m t n Nothing)  = (if m then text "mem" else empty) <+> pp t <+> pp n
    pp (Var _ m t n (Just i)) = (if m then text "mem" else empty) <+> pp t <+> pp n <+> char '=' <+> pp i

instance WithPos Var where
    pos       = vpos
    atPos v p = v{vpos = p}

instance WithName Var where
    name = varName

instance WithTypeSpec Var where
    tspec = varType
