{-# LANGUAGE ImplicitParams #-}

module IExpr(Val(..),
             Expr(..),
             scalars,
             (===),
             disj,
             conj,
             true,
             false,
             Slice,
             LExpr) where

import Data.Maybe
import Data.List

import Util hiding (name)
import TSLUtil
import Common
import IType
import IVar
import {-# SOURCE #-} ISpec

-- Value
data Val = BoolVal   Bool
         | SIntVal   Int Integer
         | UIntVal   Int Integer
         | EnumVal   String
         | PtrVal    LExpr

instance (?spec::Spec) => Typed Val where
    typ (BoolVal _)   = Bool
    typ (SIntVal w _) = SInt w
    typ (UIntVal w _) = UInt w
    typ (EnumVal n)   = Enum $ enumName $ getEnum n
    typ (PtrVal e)    = Ptr $ typ e

data Expr = EVar    String
          | EConst  Val
          | EField  Expr String
          | EIndex  Expr Expr
          | EUnOp   UOp Expr
          | EBinOp  BOp Expr Expr
          | ESlice  Expr Slice

instance (?spec::Spec) => Typed Expr where
    typ (EVar n)                               = typ $ getVar n
    typ (EConst v)                             = typ v
    typ (EField s f)                           = let Struct fs = typ s
                                                 in typ $ fromJust $ find (\(Field n _) -> n == f) fs 
    typ (EIndex a _)                           = t where Array t _ = typ a
    typ (EUnOp UMinus e)                       = SInt $ typeWidth e
    typ (EUnOp Not e)                          = Bool
    typ (EUnOp BNeg e)                         = typ e
    typ (EUnOp Deref e)                        = t where Ptr t = typ e
    typ (EUnOp AddrOf e)                       = Ptr $ typ e
    typ (EBinOp op e1 e2) | isRelBOp op        = Bool
                          | isBoolBOp op       = Bool
                          | isBitWiseBOp op    = typ e1
                          | op == BConcat      = UInt $ (typeWidth e1) + (typeWidth e2)
                          | elem op [Plus,Mul] = case (typ e1, typ e2) of
                                                         ((UInt w1), (UInt w2)) -> UInt $ max w1 w2
                                                         _                      -> SInt $ max (typeWidth e1) (typeWidth e2)
                          | op == BinMinus     = SInt $ max (typeWidth e1) (typeWidth e2)
                          | op == Mod          = typ e1
    typ (ESlice _ (l,h))                       = UInt $ h - l + 1


-- Extract all scalars from expression
scalars :: Expr -> Type -> [Expr]
scalars e (Struct fs)  = concatMap (\(Field n t) -> scalars (EField e n) t) fs
scalars e (Array  t s) = concatMap (\i -> scalars (EIndex e (EConst $ UIntVal (bitWidth $ s-1) $ fromIntegral i)) t) [0..s-1]
scalars e t            = [e]

(===) :: Expr -> Expr -> Expr
e1 === e2 = EBinOp Eq e1 e2

disj :: [Expr] -> Expr
disj [] = false
disj es = foldl' (\e1 e2 -> EBinOp Or e1 e2) (head es) (tail es)

conj :: [Expr] -> Expr
conj [] = false
conj es = foldl' (\e1 e2 -> EBinOp And e1 e2) (head es) (tail es)

true = EConst $ BoolVal True
false = EConst $ BoolVal False

type Slice = (Int, Int)

type LExpr = Expr
