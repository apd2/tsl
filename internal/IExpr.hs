{-# LANGUAGE ImplicitParams, TypeSynonymInstances, FlexibleInstances #-}

module IExpr(Val(..),
             Expr(..),
             exprSlice,
             exprScalars,
             (===),
             disj,
             conj,
             econcat,
             true,
             false,
             Slice,
             LExpr,
             exprPtrSubexpr) where

import Data.Maybe
import Data.List
import Text.PrettyPrint

import PP
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
--         | PtrVal    LExpr

instance (?spec::Spec) => Typed Val where
    typ (BoolVal _)   = Bool
    typ (SIntVal w _) = SInt w
    typ (UIntVal w _) = UInt w
    typ (EnumVal n)   = Enum $ enumName $ getEnumerator n
--    typ (PtrVal e)    = Ptr $ typ e

instance PP Val where
    pp (BoolVal True)  = text "true"
    pp (BoolVal False) = text "false"
    pp (SIntVal _ v)   = text $ show v
    pp (UIntVal _ v)   = text $ show v
    pp (EnumVal n)     = text n
--    pp (PtrVal e)      = char '&' <> pp e

type Slice = (Int, Int)

instance PP Slice where
    pp (l,h) = brackets $ pp l <> colon <> pp h

data Expr = EVar    String
          | EConst  Val
          | EField  Expr String
          | EIndex  Expr Expr
          | EUnOp   UOp Expr
          | EBinOp  BOp Expr Expr
          | ESlice  Expr Slice

instance PP Expr where
    pp (EVar n)          = pp n
    pp (EConst v)        = pp v
    pp (EField e f)      = pp e <> char '.' <> pp f
    pp (EIndex a i)      = pp a <> char '[' <> pp i <> char ']'
    pp (EUnOp op e)      = parens $ pp op <> pp e
    pp (EBinOp op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (ESlice e s)      = pp e <> pp s

instance Show Expr where
    show = render . pp

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

-- TODO: optimise slicing of concatenations
exprSlice :: (?spec::Spec) => Expr -> Slice -> Expr
exprSlice e                      (l,h) | l == 0 && h == typeWidth e - 1 = e
exprSlice (ESlice e (l',h'))     (l,h)                                  = exprSlice e (l'+l,l'+h)
exprSlice (EBinOp BConcat e1 e2) (l,h) | l > typeWidth e1 - 1           = exprSlice e2 (l - typeWidth e1, h - typeWidth e1)
                                       | h <= typeWidth e1 - 1          = exprSlice e1 (l,h)
                                       | otherwise                      = econcat [exprSlice e1 (l,typeWidth e1-1), exprSlice e2 (0, h - typeWidth e1)]
exprSlice e                      s                                      = ESlice e s

---- Extract all scalars from expression
exprScalars :: Expr -> Type -> [Expr]
exprScalars e (Struct fs)  = concatMap (\(Field n t) -> exprScalars (EField e n) t) fs
exprScalars e (Array  t s) = concatMap (\i -> exprScalars (EIndex e (EConst $ UIntVal (bitWidth $ s-1) $ fromIntegral i)) t) [0..s-1]
exprScalars e t            = [e]

(===) :: Expr -> Expr -> Expr
e1 === e2 = EBinOp Eq e1 e2

disj :: [Expr] -> Expr
disj [] = false
disj es = foldl' (\e1 e2 -> EBinOp Or e1 e2) (head es) (tail es)

conj :: [Expr] -> Expr
conj [] = false
conj es = foldl' (\e1 e2 -> EBinOp And e1 e2) (head es) (tail es)

-- TODO: merge adjacent expressions
econcat :: [Expr] -> Expr
econcat [e]        = e
econcat (e1:e2:es) = econcat $ (EBinOp BConcat e1 e2):es

true = EConst $ BoolVal True
false = EConst $ BoolVal False

type LExpr = Expr

-- Subexpressions dereferenced inside the expression
exprPtrSubexpr :: Expr -> [Expr]
exprPtrSubexpr (EField e _)     = exprPtrSubexpr e
exprPtrSubexpr (EIndex a i)     = exprPtrSubexpr a ++ exprPtrSubexpr i
exprPtrSubexpr (EUnOp Deref e)  = e:(exprPtrSubexpr e)
exprPtrSubexpr (EUnOp _ e)      = exprPtrSubexpr e
exprPtrSubexpr (EBinOp _ e1 e2) = exprPtrSubexpr e1 ++ exprPtrSubexpr e2
exprPtrSubexpr (ESlice e s)     = exprPtrSubexpr e
exprPtrSubexpr e                = []
