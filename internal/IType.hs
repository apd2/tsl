module IType(Field(..),
             Type(..),
             Typed(..),
             typeWidth,
             Enumeration(..)) where

data Field = Field String Type deriving (Eq)

instance Typed Field where
    typ (Field _ t) = t

data Type = Bool
          | SInt     Int
          | UInt     Int
          | Enum     String
          | Struct   [Field]
          | Ptr      Type
          | Array    Type Int
          deriving (Eq)

twidth :: Type -> Int
twidth (SInt w) = w
twidth (UInt w) = w
twidth _        = error "twidth undefined"

class Typed a where
    typ :: a -> Type

instance Typed Type where
    typ = id

typeWidth :: (Typed a) => a -> Int
typeWidth = twidth . typ


data Enumeration = Enumeration { enumName  :: String
                               , enumEnums :: [String]
                               }

