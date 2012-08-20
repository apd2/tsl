{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Expr(Expr(ETerm,ELit,EBool,EApply,EField,EPField,EIndex,EUnOp,EBinOp,ETernOp,ECase,ECond,ESlice,EStruct,ENonDet),
            ConstExpr, 
            MethodRef(MethodRef),
            Radix(..),
            UOp(..),
            BOp(..)) where

import Text.PrettyPrint
import Numeric
import Data.Char

import PP
import Pos
import Name

-- Common types
type Slice = (ConstExpr, ConstExpr)  -- low,high
instance PP Slice where
    pp (l,h) = brackets $ pp l <> colon <> pp h 

data Radix = Rad2 | Rad8 | Rad10 | Rad16
instance PP Radix where
    pp Rad2  = text "'b"
    pp Rad8  = text "'o"
    pp Rad10 = text "'d"
    pp Rad16 = text "'h"

data MethodRef = MethodRef Pos [Ident]

instance WithPos MethodRef where
    pos (MethodRef p _)     = p
    atPos (MethodRef _ m) p = MethodRef p m

instance PP MethodRef where
    pp (MethodRef _ m) = hcat $ punctuate (char '.') (map pp m)


data UOp = UMinus 
         | Not 
         | BNeg
         | Deref
         | AddrOf
instance PP UOp where
    pp UMinus = char '-'
    pp Not    = char '!'
    pp BNeg   = char '~'
    pp Deref  = char '*'
    pp AddrOf = char '&'

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
         | Plus 
         | BinMinus 
         | Mod
         | Mul
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
    pp Plus     = text "+"
    pp BinMinus = text "-"
    pp Mod      = text "%"
    pp Mul      = text "*"



-- Expressions 
data Expr = ETerm   {epos::Pos, ssym::StaticSym}
          | ELit    {epos::Pos, width::(Maybe Int), rad::Radix, ival::Integer}
          | EBool   {epos::Pos, bval::Bool}
          | EApply  {epos::Pos, mref::MethodRef, args::[Expr]}
          | EField  {epos::Pos, struct::Expr, field::Ident}
          | EPField {epos::Pos, struct::Expr, field::Ident}
          | EIndex  {epos::Pos, arr::Expr, idx::Expr}
          | EUnOp   {epos::Pos, uop::UOp, arg1::Expr}
          | EBinOp  {epos::Pos, bop::BOp, arg1::Expr, arg2::Expr}
          | ETernOp {epos::Pos, arg1::Expr, arg2::Expr, arg3::Expr}
          | ECase   {epos::Pos, caseexpr::Expr, cases::[(Expr, Expr)], def::(Maybe Expr)}
          | ECond   {epos::Pos, cases::[(Expr, Expr)], def::(Maybe Expr)}
          | ESlice  {epos::Pos, slexpr::Expr, slice::Slice}
          | EStruct {epos::Pos, typename::StaticSym, fields::(Either [(Ident, Expr)] [Expr])} -- either named or anonymous list of fields
          | ENonDet {epos::Pos}

instance PP Expr where
    pp (ETerm _ s)              = pp s
    pp (ELit _ w r v)           = pp w <> pp r <> 
                                  case r of
                                       Rad2  -> text $ showIntAtBase 2 intToDigit v ""
                                       Rad8  -> text $ showOct v ""
                                       Rad10 -> pp v
                                       Rad16 -> text $ showHex v ""
    pp (EBool _ True)            = text "true"
    pp (EBool _ False)           = text "false"
    pp (EApply _ m args)         = pp m <+> (parens $ hsep $ punctuate comma $ map pp args)
    pp (EIndex _ e i)            = pp e <> char '[' <> pp i <> char ']'
    pp (EField _ e f)            = pp e <> char '.' <> pp f
    pp (EPField _ e f)           = pp e <> text "->" <> pp f
    pp (EUnOp _ op e)            = parens $ pp op <> pp e
    pp (EBinOp _ op e1 e2)       = parens $ pp e1 <+> pp op <+> pp e2
    pp (ETernOp _ c e1 e2)       = parens $ pp c <+> char '?' <+> pp e2 <+> colon <+> pp e2
    pp (ECase _ e cs def)        = text "case" <+> (parens $ pp e) <+> (braces' $ ppcs $+$ ppdef)
                                       where ppcs = vcat $ map (\(c,e') -> pp c <> colon <+> pp e' <> semi) cs
                                             ppdef = text "default" <> colon <+> pp def <> semi
    pp (ECond _ cs def)          = text "cond" <+> (braces' $ ppcs $+$ ppdef)
                                       where ppcs = vcat $ map (\(c,e') -> pp c <> colon <+> pp e' <> semi) cs
                                             ppdef = text "default" <> colon <+> pp def <> semi
    pp (ESlice _ e s)            = pp e <> pp s
    pp (EStruct _ t (Left fs))   = pp t <+> (braces $ hcat $ punctuate comma $ 
                                             map (\(n,e) -> char '.' <> pp n <+> char '=' <+> pp e) fs)
    pp (EStruct _ t (Right fs))  = pp t <+> (braces' $ vcat $ punctuate comma $ map pp fs)
    pp (ENonDet _)               = char '*'

instance WithPos Expr where
    pos       = epos
    atPos e p = e{epos = p}

type ConstExpr = Expr


