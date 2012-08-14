{-# LANGUAGE ImplicitParams, FlexibleContexts, UndecidableInstances #-}

module TypeSpec(TypeSpec, TypeDecl, Enumerator, TypeNS) where

import Prelude hiding ((!!))
import Pos
import Type
import Name
import qualified NS
import qualified Expr as E

-- Type spec
data Enumerator = Enumerator { epos  :: Pos
                             , ename :: Ident
                             , eval  :: E.ConstExpr}

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

class (NS.NS a TypeSpec) => TypeNS a where
    (!) :: a -> Ident -> TypeSpec
    (!) = (NS.!)
    (!!) :: a -> [Ident] -> TypeSpec
    (!!) = (NS.!!)

instance WithPos TypeSpec where
    pos = tpos

instance (TypeNS a, ?types::a) => WithType TypeSpec where
    typ (BoolSpec _)        = Bool
    typ (SIntSpec _ w)      = SInt w
    typ (UIntSpec _ w)      = UInt w
    typ (StructSpec _ fs)   = Struct $ map (\(Ident _ n,s) -> (n, typ s)) fs 
    typ (EnumSpec _ es)     = Enum $ map (\(Enumerator _ (Ident _ n) v) -> (n, E.evalInt v)) es
    typ (PtrSpec _ t)       = Ptr $ typ t
    typ (ArraySpec _ t l)   = Array (typ t) l
    typ (UserTypeSpec _ t)  = typ (?types !! t)


-- Type declaration
data TypeDecl = TypeDecl { dname :: Ident
                         , dpos  :: Pos
                         , dspec :: TypeSpec}

instance WithPos TypeDecl where
    pos = dpos

instance WithName TypeDecl where
    name = dname

instance (TypeNS a, ?types::a) => WithType TypeDecl where
    typ = typ . dspec
