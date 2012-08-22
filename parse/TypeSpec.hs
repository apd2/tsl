{-# LANGUAGE ImplicitParams, FlexibleContexts, UndecidableInstances #-}

module TypeSpec(TypeSpec(BoolSpec,SIntSpec,UIntSpec,StructSpec,EnumSpec,PtrSpec,ArraySpec,UserTypeSpec,TemplateTypeSpec), 
                WithTypeSpec(..),
                TypeDecl(TypeDecl), 
                Enumerator(Enumerator,enumVal),
                Field(Field)) where

import Text.PrettyPrint
import Control.Monad.Error

import PP
import Pos
import Name
import Expr

-- Type spec
data Enumerator = Enumerator { epos    :: Pos
                             , ename   :: Ident
                             , enumVal :: Maybe ConstExpr}

instance PP Enumerator where
    pp (Enumerator _ n Nothing)  = pp n
    pp (Enumerator _ n (Just e)) = pp n <+> char '=' <+> pp e


instance WithPos Enumerator where
    pos       = epos
    atPos e p = e{epos = p}

instance WithName Enumerator where
    name = ename


-- Struct field
data Field = Field { fpos  :: Pos
                   , ftyp  :: TypeSpec
                   , fname :: Ident}

instance PP Field where
    pp (Field _ t n) = pp t <+> pp n

instance WithPos Field where
    pos       = fpos
    atPos f p = f{fpos = p}

instance WithName Field where
    name = fname

instance WithTypeSpec Field where
    tspec = ftyp

data TypeSpec = BoolSpec         {tpos :: Pos}
              | SIntSpec         {tpos :: Pos, width  :: Int}
              | UIntSpec         {tpos :: Pos, width  :: Int}
              | StructSpec       {tpos :: Pos, fields :: [Field]}
              | EnumSpec         {tpos :: Pos, enums  :: [Enumerator]}
              | PtrSpec          {tpos :: Pos, ptype  :: TypeSpec}
              | ArraySpec        {tpos :: Pos, eltype :: TypeSpec, len :: Expr}
              | UserTypeSpec     {tpos :: Pos, tname  :: StaticSym}
              | TemplateTypeSpec {tpos :: Pos, tmname :: Ident}

instance PP TypeSpec where
    pp (BoolSpec _)           = text "bool"
    pp (SIntSpec _ i)         = text "sint" <> char '<' <> pp i <> char '>'
    pp (UIntSpec _ i)         = text "uint" <> char '<' <> pp i <> char '>'
    pp (StructSpec _ fs)      = text "struct" <+> (braces $ nest' $ vcat $ map ((<> semi) . pp) fs)
    pp (EnumSpec _ es)        = text "enum" <+> (braces $ nest' $ vcat $ punctuate comma $ map pp es)
    pp (PtrSpec _ t)          = pp t <> char '*'
    pp (ArraySpec _ t l)      = pp t <> (brackets $ pp l)
    pp (UserTypeSpec _ n)     = pp n
    pp (TemplateTypeSpec _ n) = text "template" <+> pp n

instance Show TypeSpec where
    show = render . pp

instance WithPos TypeSpec where
    pos       = tpos
    atPos t p = t{tpos = p}

class WithTypeSpec a where
    tspec :: a -> TypeSpec

instance WithTypeSpec TypeSpec where
    tspec = id

-- Type declaration
data TypeDecl = TypeDecl { dpos  :: Pos
                         , dspec :: TypeSpec
                         , dname :: Ident}

instance PP TypeDecl where
    pp (TypeDecl _ t n) = text "typedef" <+> pp t <+> pp n

instance WithPos TypeDecl where
    pos       = dpos
    atPos t p = t{dpos=p}

instance WithName TypeDecl where
    name = dname

instance WithTypeSpec TypeDecl where
    tspec = dspec


