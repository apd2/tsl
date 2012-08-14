module Type(Type(..), WithType(..)) where

data Type = Bool
          | SInt Int
          | UInt Int
          | Struct [(String,Type)]
          | Enum [(String, Integer)]
          | Ptr Type
          | Array Type Integer


class WithType a where
    typ :: a -> Type
