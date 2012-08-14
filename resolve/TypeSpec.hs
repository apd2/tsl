module TypeSpec(TypeSpec, TypeDecl, Enumerator) where

import Pos
import Type
import qualified Expr as E

-- Type spec
type Enumerator = Enumerator { epos  :: Pos
                             , ename :: Ident
                             , eval  :: E.ConstExpr)

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
              | NamedTypeSpec {tpos :: Pos, tname :: ScopedIdent}

instance WithPos TypeSpec where
    pos = tpos

instance WithType TypeSpec where
    typ (BoolSpec _)        = Bool
    typ (SIntSpec _ w)      = SInt w
    typ (UIntSpec _ w)      = UInt w
    typ (StructSpec _ fs)   = Struct $ map (\(Ident _ n,s) -> (n, typ s)) fs 
    typ (EnumSpec _ es)     = Enum $ map (\(Ident _ n, v) -> (n, E.evalInt v)) es
    typ (PtrSpec _ t)       = Ptr $ typ t
    typ (ArraySpec _ t l)   = Array (typ t) l
    typ (NamedTypeSpec _ t) = typ t

instance NS TypeSpec Obj where
    lookup (StructSpec _ fs) (Field n) = fmap (ObjType . snd) $ find ((==n) . fst) fs 
    lookup (ArraySpec _ t l) (Index _) = Just $ ObjType t
    lookup _ _                         = Nothing


instance StaticNS TypeSpec Obj where
    slookup (EnumSpec _ es) i = fmap (ObjEnum . snd) $ find ((==n) . fst) es
    slookup _ _               = Nothing


-- Type declaration
data TypeDecl = TypeDecl { dname :: Ident
                         , dpos  :: Pos
                         , dspec :: TypeSpec}

instance WithPos TypeDecl where
    pos = dpos

instance WithName TypeDecl where
    name = dname

instance WithType TypeDecl where
    typ = typ dspec

instance StaticNS TypeDecl Obj where
    slookup d = slookup (dspec d)


