-- Common data types

module Common where

import Text.PrettyPrint

import PP

data Radix = Rad2 
           | Rad8 
           | Rad10 
           | Rad16 
           deriving (Eq)

data UOp = UMinus 
         | Not 
         | BNeg
         | Deref
         | AddrOf
         deriving (Eq)

instance PP UOp where
    pp UMinus = char '-'
    pp Not    = char '!'
    pp BNeg   = char '~'
    pp Deref  = char '*'
    pp AddrOf = char '&'

instance Show UOp where
    show = render . pp

data BOp = Eq 
         | Neq 
         | Lt 
         | Gt 
         | Lte 
         | Gte
         | And 
         | Or 
         | Imp
         | BAnd 
         | BOr 
         | BXor
         | BConcat
         | Plus 
         | BinMinus 
         | Mod
         | Mul
         deriving(Eq)

instance PP BOp where
    pp Eq       = text "=="
    pp Neq      = text "!="
    pp Lt       = text "<"
    pp Gt       = text ">"
    pp Lte      = text "<="
    pp Gte      = text ">="
    pp And      = text "&&"
    pp Or       = text "||"
    pp Imp      = text "->"
    pp BAnd     = text "&"
    pp BOr      = text "|"
    pp BXor     = text "^"
    pp BConcat  = text "++"
    pp Plus     = text "+"
    pp BinMinus = text "-"
    pp Mod      = text "%"
    pp Mul      = text "*"

instance Show BOp where
    show = render . pp
