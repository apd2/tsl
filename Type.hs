module Type(Type(..), WithType(..)) where

data Type = Bool
          | SInt Int
          | UInt Int
          | Struct [(String,Type)]
          | Enum [(String, Integer)]
          | Ptr Type
          | Array Type Integer


--class WithType a where
--    typ :: a -> Type
--

--instance (TypeNS a, ?types::a) => WithType TypeSpec where
--    typ (BoolSpec _)        = Bool
--    typ (SIntSpec _ w)      = SInt w
--    typ (UIntSpec _ w)      = UInt w
--    typ (StructSpec _ fs)   = Struct $ map (\(Ident _ n,s) -> (n, typ s)) fs 
--    typ (EnumSpec _ es)     = Enum $ map (\(Enumerator _ (Ident _ n) v) -> (n, E.evalInt v)) es
--    typ (PtrSpec _ t)       = Ptr $ typ t
--    typ (ArraySpec _ t l)   = Array (typ t) l
--    typ (UserTypeSpec _ t)  = typ (?types !! t)


