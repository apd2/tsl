{-# LANGUAGE ImplicitParams, FlexibleContexts, UndecidableInstances #-}

module TypeSpec(TypeSpec(BoolSpec,SIntSpec,UIntSpec,StructSpec,EnumSpec,PtrSpec,ArraySpec,UserTypeSpec), 
                WithType(..),
                TypeDecl(TypeDecl), 
                Enumerator(Enumerator,enumVal)) where

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

data TypeSpec = BoolSpec      {tpos :: Pos}
              | SIntSpec      {tpos :: Pos, width :: Int}
              | UIntSpec      {tpos :: Pos, width :: Int}
              | StructSpec    {tpos :: Pos, fields :: [(TypeSpec,Ident)]}
              | EnumSpec      {tpos :: Pos, enums :: [Enumerator]}
              | PtrSpec       {tpos :: Pos, ptype :: TypeSpec}
              | ArraySpec     {tpos :: Pos, eltype :: TypeSpec, len :: Expr}
              | UserTypeSpec  {tpos :: Pos, tname :: StaticSym}

instance PP TypeSpec where
    pp (BoolSpec _)       = text "bool"
    pp (SIntSpec _ i)     = text "sint" <> char '<' <> pp i <> char '>'
    pp (UIntSpec _ i)     = text "uint" <> char '<' <> pp i <> char '>'
    pp (StructSpec _ fs)  = text "struct" <+> (braces $ nest' $ vcat $ map ((<> semi) . ppfield) fs)
                                where ppfield (t,n) = pp t <+> pp n
    pp (EnumSpec _ es)    = text "enum" <+> (braces $ nest' $ vcat $ punctuate comma $ map pp es)
    pp (PtrSpec _ t)      = pp t <> char '*'
    pp (ArraySpec _ t l)  = pp t <> (brackets $ pp l)
    pp (UserTypeSpec _ n) = pp n

instance WithPos TypeSpec where
    pos       = tpos
    atPos t p = t{tpos = p}

class WithType a where
    typ :: a -> TypeSpec

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

instance WithType TypeDecl where
    typ = dspec
