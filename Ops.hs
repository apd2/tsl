-- Common data types

module Ops where

import Text.PrettyPrint
import Data.Bits
import Data.List

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

isRelBOp :: BOp -> Bool
isRelBOp op = elem op [Eq,Neq,Lt,Gt,Lte,Gte] 

isBoolBOp :: BOp -> Bool
isBoolBOp op = elem op [And,Or,Imp]

isArithBOp :: BOp -> Bool
isArithBOp op = elem op [BAnd,BOr,BXor,BConcat,Plus,BinMinus,Mod,Mul]

isArithUOp :: UOp -> Bool
isArithUOp op = elem op [UMinus,BNeg]

isBitWiseBOp :: BOp -> Bool
isBitWiseBOp op = elem op [BAnd,BOr,BXor]

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

-- Determine type of result of arith expression.
-- Type of each operand and the result is described as (signed?, width)
arithBOpType :: BOp -> (Bool,Int) -> (Bool,Int) -> (Bool,Int)
arithBOpType op       (s1,w1) (s2,w2) | elem op [BAnd,BOr,BXor]     = (s1,w1)
arithBOpType BConcat  (s1,w1) (s2,w2)                               = (False, w1 + w2)
arithBOpType op       (s1,w1) (s2,w2) | elem op [Plus,Mul,BinMinus] = case (s1, s2) of
                                                                           (False, False) -> (False, max w1 w2)
                                                                           _              -> (True,  max w1 w2)
arithBOpType Mod      (s1,w1) (s2,w2)                               = (s1,w1)

arithUOpType :: UOp -> (Bool,Int) -> (Bool,Int)
arithUOpType BNeg   (s,w) = (s,w)
arithUOpType UMinus (s,w) = (True,w)

-- Perform binary arithmetic operation
-- Takes integer arguments and their widths
arithBOp :: BOp -> (Integer,Bool,Int) -> (Integer,Bool,Int) -> (Integer,Bool,Int)
arithBOp op (i1,s1,w1) (i2,s2,w2)   | elem op [BAnd,BOr,BXor] = (i,s,w)
    where (s,w) = arithBOpType op (s1,w1) (s2,w2)
          f = case op of
                   BAnd -> (&&)
                   BOr  -> (||)
                   BXor -> (\b1 b2 -> (b1 && not b2) || (b2 && not b1))
          i = foldl' (\v idx -> case f (testBit i1 idx) (testBit i2 idx) of
                                     True  -> setBit v idx
                                     False -> v) 
                     0 [0..w - 1]

arithBOp BConcat (i1,s1,w1) (i2,s2,w2)  = (i,s,w)
    where (s,w) = arithBOpType BConcat (s1,w1) (s2,w2)
          i1' = abs i1
          i2' = abs i2
          i = i1' + (i2' `shiftL` w1)

arithBOp op (i1,s1,w1) (i2,s2,w2)   | elem op [Plus,BinMinus,Mod,Mul] = (i',s,w)
    where (s,w) = arithBOpType op (s1,w1) (s2,w2)
          i = case op of
                   Plus     -> i1 + i2
                   BinMinus -> i1 - i2
                   Mod      -> mod i1 i2
                   Mul      -> i1 * i2
              .&.
              (sum $ map bit [0..w - 1])
          i' = if s && testBit i (w-1)
                  then - ((foldl' (\x idx -> complementBit x idx) i [0..w-1]) + 1)
                  else i
-- Perform unary arithmetic operation
-- Takes integer argument and width
arithUOp :: UOp -> (Integer, Bool, Int) -> (Integer, Bool, Int)
arithUOp BNeg   (i,s,w) = (foldl' (\v idx -> complementBit v idx) i [0..w - 1], s, w)
arithUOp UMinus (i,s,w) = ((-i) .&. (sum $ map bit [0..w - 1]), True, w)
