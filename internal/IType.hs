module IType(Field(..),
             Type(..),
             Typed(..),
             typeWidth,
             isSigned,
             isInt,
             isBool,
             isPtr,
             isEnum,
             isScalar,
             Enumeration(..)) where

import Text.PrettyPrint

import PP
import TSLUtil

data Field = Field String Type deriving (Eq,Ord)

instance PP Field where
    pp (Field n t) = pp t <+> text n

instance Typed Field where
    typ (Field _ t) = t

data Type = Bool
          | SInt     Int
          | UInt     Int
          | Enum     String
          | Struct   [Field]
          | Ptr      Type
          | Array    Type Int
          | VarArray Type
          deriving (Eq,Ord)

instance PP Type where
    pp Bool         = text "bool"
    pp (SInt i)     = text "sint" <> char '<' <> pp i <> char '>'
    pp (UInt i)     = text "uint" <> char '<' <> pp i <> char '>'
    pp (Enum e)     = text e
    pp (Struct fs)  = text "struct" <+> (braces $ nest' $ vcat $ map ((<> semi) . pp) fs)
    pp (Ptr t)      = pp t <> char '*'
    pp (Array t l)  = pp t <> char '[' <> pp l <> char ']'
    pp (VarArray t) = pp t <> char '[' <> char ']'

instance Show Type where
    show = render . pp

twidth :: Type -> Int
twidth Bool        = 1
twidth (SInt w)    = w
twidth (UInt w)    = w
twidth (Enum e)    = bitWidth $ length e - 1
twidth (Array t l) = l * twidth t
twidth (Struct fs) = sum $ map typeWidth fs
twidth t           = error $ "twidth " ++ show t ++ " undefined"

class Typed a where
    typ :: a -> Type

instance Typed Type where
    typ = id

typeWidth :: (Typed a) => a -> Int
typeWidth = twidth . typ

isSigned :: (Typed a) => a -> Bool
isSigned x = case typ x of
                  SInt _ -> True
                  UInt _ -> False


isInt :: (Typed a) => a -> Bool
isInt x = case typ x of
               SInt _ -> True
               UInt _ -> True
               _      -> False

isEnum :: (Typed a) => a -> Bool
isEnum x = case typ x of
                Enum _ -> True
                _      -> False

isPtr :: (Typed a) => a -> Bool
isPtr x = case typ x of
               Ptr _ -> True
               _     -> False

isBool :: (Typed a) => a -> Bool
isBool x = typ x == Bool 

isScalar :: (Typed a) => a -> Bool
isScalar x = case typ x of
                  Bool   -> True
                  SInt _ -> True
                  UInt _ -> True
                  Enum _ -> True
                  Ptr _  -> True
                  _      -> False

data Enumeration = Enumeration { enumName  :: String
                               , enumEnums :: [String]
                               }

instance PP Enumeration where
    pp (Enumeration n es) = text "enum" <+> text n <+> 
                            (braces' $ vcat $ map ((<> semi) . text) es)
