{-# LANGUAGE ImplicitParams, FlexibleContexts, UndecidableInstances #-}

module TypeSpec(TypeSpec(StructSpec), 
                WithType(..),
                TypeDecl, 
                Enumerator(enumVal)) where

import Pos
import Name
import Expr

-- Type spec
data Enumerator = Enumerator { epos    :: Pos
                             , ename   :: Ident
                             , enumVal :: ConstExpr}

instance WithPos Enumerator where
    pos = epos

instance WithName Enumerator where
    name = ename

data TypeSpec = BoolSpec      {tpos :: Pos}
              | SIntSpec      {tpos :: Pos, width :: Int}
              | UIntSpec      {tpos :: Pos, width :: Int}
              | StructSpec    {tpos :: Pos, fields :: [(Ident,TypeSpec)]}
              | EnumSpec      {tpos :: Pos, enums :: [Enumerator]}
              | PtrSpec       {tpos :: Pos, ptype :: TypeSpec}
              | ArraySpec     {tpos :: Pos, eltype :: TypeSpec, len :: Integer}
              | UserTypeSpec  {tpos :: Pos, tname :: GStaticSym}

instance WithPos TypeSpec where
    pos = tpos

class WithType a where
    typ :: a -> TypeSpec

-- Type declaration
data TypeDecl = TypeDecl { dname :: Ident
                         , dpos  :: Pos
                         , dspec :: TypeSpec}

instance WithPos TypeDecl where
    pos = dpos

instance WithName TypeDecl where
    name = dname

instance WithType TypeDecl where
    typ = dspec
