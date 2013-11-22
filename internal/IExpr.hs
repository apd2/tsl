{-# LANGUAGE ImplicitParams, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module IExpr(LVal(..),
             Val(..),
             Expr(..),
             lvalToExpr,
             valSlice,
             valDefault,
             parseVal,
             exprSlice,
             exprScalars,
             exprVars,
             exprPad,
             (===),
             (/==),
             (==>),
             (.<=),
             (.%),
             uminus,
             disj,
             conj,
             neg,
             land,
             lor,
             plus,
             plusmod,
             econcat,
             true,
             false,
             Slice,
             isConstExpr,
             evalConstExpr,
             evalLExpr,
             isMemExpr,
             exprPtrSubexpr,
             arrLengthBits,
             mapExpr) where

import Data.Maybe
import Data.List
import Data.Bits hiding (isSigned)
import Text.PrettyPrint
import Control.Monad.Error
import qualified Text.Parsec as P

import Util
import Grammar
import PP
import TSLUtil
import Ops
import IType
import IVar
import {-# SOURCE #-} ISpec
import Type (arrLengthBits)

-- variable address
data LVal = LVar String
          | LField LVal String
          | LIndex LVal Integer
          deriving (Eq,Ord)

lvalToExpr :: LVal -> Expr 
lvalToExpr (LVar n)     = EVar n
lvalToExpr (LField s f) = EField (lvalToExpr s) f
lvalToExpr (LIndex a i) = EIndex (lvalToExpr a) (EConst $ UIntVal 32 i)

instance (?spec::Spec) => Typed LVal where
    typ (LVar n)     = typ $ getVar n
    typ (LField s n) = let Struct fs = typ s
                       in typ $ fromJust $ find (\(Field f _) -> n == f) fs 
    typ (LIndex a _) = t where Array t _ = typ a

instance PP LVal where
    pp (LVar n)     = pp n
    pp (LField s f) = pp s <> char '.' <> pp f
    pp (LIndex a i) = pp a <> char '[' <> pp i <> char ']'

-- Value
data Val = BoolVal   Bool
         | SIntVal   {ivalWidth::Int, ivalVal::Integer}
         | UIntVal   {ivalWidth::Int, ivalVal::Integer}
         | EnumVal   String
         | PtrVal    LVal
         | NullVal   Type
         deriving (Eq, Ord)

ivalIsSigned :: Val -> Bool
ivalIsSigned (SIntVal _ _) = True
ivalIsSigned (UIntVal _ _) = False

instance (?spec::Spec) => Typed Val where
    typ (BoolVal _)   = Bool
    typ (SIntVal w _) = SInt w
    typ (UIntVal w _) = UInt w
    typ (EnumVal n)   = Enum $ enumName $ getEnumerator n
    typ (PtrVal a)    = Ptr $ typ a
    typ (NullVal t)   = t

instance PP Val where
    pp (BoolVal True)  = text "true"
    pp (BoolVal False) = text "false"
    pp (SIntVal _ v)   = text $ show v
    pp (UIntVal _ v)   = text $ show v
    pp (EnumVal n)     = text n
    pp (PtrVal a)      = char '&' <> pp a
    pp (NullVal _)     = text "NULL"

instance Show Val where
    show = render . pp

type Slice = (Int, Int)

instance PP Slice where
    pp (l,h) = brackets $ pp l <> colon <> pp h

-- Default value of a type
valDefault :: (?spec::Spec, Typed a) => a -> Val
valDefault x = case typ x of
                    Bool      -> BoolVal False
                    SInt w    -> SIntVal w 0
                    UInt w    -> UIntVal w 0  
                    Enum n    -> EnumVal $ head $ enumEnums $ getEnumeration n
                    Struct _  -> error "valDefault Struct"
                    Ptr t     -> NullVal t
                    Array _ _ -> error "valDefault Array"


valSlice :: Val -> Slice -> Val
valSlice v (l,h) = UIntVal (h - l + 1)
                   $ foldl' (\a idx -> case testBit (ivalVal v) idx of
                                            True  -> a + bit (idx - l)
                                            False -> a)
                   0 [l..h]

parseVal :: (MonadError String me, ?spec::Spec) => Type -> String -> me Val
parseVal (SInt w) str = do
    (w',_,_,v) <- case P.parse litParser "" str of
                       Left e  -> throwError $ show e
                       Right x -> return x
    when  (w' > w) $ throwError $ "Width mismatch"
    return $ SIntVal w v 
parseVal (UInt w) str = do
    (w',s,_,v) <- case P.parse litParser "" str of
                       Left e  -> throwError $ show e
                       Right x -> return x
    when (w' > w) $ throwError $ "Width mismatch"
    when s $ throwError $ "Sign mismatch"
    return $ UIntVal w v 
parseVal Bool str =
    case P.parse boolParser "" str of
         Left e  -> throwError $ show e
         Right b -> return $ BoolVal b
parseVal (Enum n) str = 
    case lookupEnumerator str of
         Nothing    -> throwError $ "Invalid enumerator: " ++ str
         Just enum  -> if' (enumName enum == n) (return $ EnumVal str)
                       $ throwError $ "Enumerator type mismatch" 

data Expr = EVar      String
          | EConst    Val
          | EField    Expr String
          | EIndex    Expr Expr
          | ERange    Expr (Expr, Expr)
          | ELength   Expr              -- Expr must be a VarArray
          | EUnOp     UOp Expr
          | EBinOp    BOp Expr Expr
          | ESlice    Expr Slice
          | ERel      String [Expr]
          deriving (Eq, Ord)

instance PP Expr where
    pp (EVar n)          = pp n
    pp (EConst v)        = pp v
    pp (EField e f)      = pp e <> char '.' <> pp f
    pp (EIndex a i)      = pp a <> char '[' <> pp i <> char ']'
    pp (ERange a (f,l))  = pp a <> char '[' <> pp f <> text "##" <> pp l <> char ']'
    pp (ELength a)       = char '#' <> pp a
    pp (EUnOp op e)      = parens $ pp op <> pp e
    pp (EBinOp op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (ESlice e s)      = pp e <> pp s
    pp (ERel n as)       = char '?' <> pp n <> (parens $ hcat $ punctuate (text ", ") $ map pp as)

instance Show Expr where
    show = render . pp

instance (?spec::Spec) => Typed Expr where
    typ (EVar n)                               = typ $ getVar n
    typ (EConst v)                             = typ v
    typ (EField s f)                           = let Struct fs = typ s
                                                 in typ $ fromJust $ find (\(Field n _) -> n == f) fs 
    typ (EIndex a _)                           = case typ a of
                                                      Array t _  -> t
                                                      VarArray t -> t
    typ (ERange a _)                           = case typ a of
                                                      Array t _  -> VarArray t
                                                      VarArray t -> VarArray t
    typ (ELength _)                            = UInt arrLengthBits
    typ (EUnOp op e) | isArithUOp op           = if s 
                                                    then SInt w
                                                    else UInt w
                                                 where (s,w) = arithUOpType op (isSigned e, typeWidth e)
    typ (EUnOp Not _)                          = Bool
    typ (EUnOp Deref e)                        = t where Ptr t = typ e
    typ (EUnOp AddrOf e)                       = Ptr $ typ e
    typ (EBinOp op e1 e2) | isRelBOp op        = Bool
                          | isBoolBOp op       = Bool
                          | isBitWiseBOp op    = typ e1
                          | isArithBOp op      = if s 
                                                    then SInt w
                                                    else UInt w
                                                 where (s,w) = arithBOpType op (s1,w1) (s2,w2)
                                                       (s1,w1) = (isSigned e1, typeWidth e1)
                                                       (s2,w2) = (isSigned e1, typeWidth e2)
    typ (ESlice _ (l,h))                       = UInt $ h - l + 1
    typ (ERel _ _)                             = Bool

-- TODO: optimise slicing of concatenations
exprSlice :: (?spec::Spec) => Expr -> Slice -> Expr
exprSlice e                      (l,h) | l == 0 && h == typeWidth e - 1 = e
exprSlice (ESlice e (l',_))      (l,h)                                  = exprSlice e (l'+l,l'+h)
exprSlice (EBinOp BConcat e1 e2) (l,h) | l > typeWidth e1 - 1           = exprSlice e2 (l - typeWidth e1, h - typeWidth e1)
                                       | h <= typeWidth e1 - 1          = exprSlice e1 (l,h)
                                       | otherwise                      = econcat [exprSlice e1 (l,typeWidth e1-1), exprSlice e2 (0, h - typeWidth e1)]
exprSlice e                      s                                      = ESlice e s

-- Extract all scalars from expression
exprScalars :: Expr -> Type -> [Expr]
exprScalars e (Struct fs)  = concatMap (\(Field n t) -> exprScalars (EField e n) t) fs
exprScalars e (Array  t s) = concatMap (\i -> exprScalars (EIndex e (EConst $ UIntVal (bitWidth $ s-1) $ fromIntegral i)) t) [0..s-1]
exprScalars e (VarArray _) = error $ "exprScalars VarArray " ++ show e
exprScalars e _            = [e]

-- Variables involved in the expression
exprVars :: (?spec::Spec) => Expr -> [Var]
exprVars = nub . exprVars'

exprVars' :: (?spec::Spec) => Expr -> [Var]
exprVars' (EVar n)         = [getVar n]
exprVars' (EConst _)       = []
exprVars' (EField e _)     = exprVars' e
exprVars' (EIndex a i)     = exprVars' a ++ exprVars' i
exprVars' (ERange a (f,l)) = exprVars' a ++ exprVars' f ++ exprVars' l
exprVars' (ELength a)      = exprVars' a
exprVars' (EUnOp _ e)      = exprVars' e
exprVars' (EBinOp _ e1 e2) = exprVars' e1 ++ exprVars' e2
exprVars' (ESlice e _)     = exprVars' e
exprVars' (ERel _ as)      = concatMap exprVars' as

(===) :: Expr -> Expr -> Expr
e1 === e2 = EBinOp Eq e1 e2

(/==) :: Expr -> Expr -> Expr
e1 /== e2 = EBinOp Neq e1 e2

(==>) :: Expr -> Expr -> Expr
e1 ==> e2 = EBinOp Imp e1 e2

uminus :: Expr -> Expr
uminus = EUnOp UMinus

(.<=) :: Expr -> Expr -> Expr
e1 .<= e2 = EBinOp Lt e1 e2

disj :: [Expr] -> Expr
disj [] = false
disj es = foldl' (\e1 e2 -> if' (e1 == false) e2 $ if' (e2 == false) e1 $ if' ((e1 == true) || (e2 == true)) true $ EBinOp Or e1 e2) (head es) (tail es)

conj :: [Expr] -> Expr
conj [] = false
conj es = foldl' (\e1 e2 -> if' (e1 == true) e2 $ if' (e2 == true) e1 $ if' ((e1 == false) || (e2 == false)) false $ EBinOp And e1 e2) (head es) (tail es)

neg :: Expr -> Expr
neg = EUnOp Not

land :: Expr -> Expr -> Expr
land = EBinOp And

lor :: Expr -> Expr -> Expr
lor = EBinOp Or

plus :: [Expr] -> Expr
plus [e] = e
plus (e:es) = EBinOp Plus e $ plus es

(.%) :: Expr -> Expr -> Expr
(.%) e1 e2 = EBinOp Mod e1 e2

-- extend arguments to fit array index and sum them modulo array length
plusmod :: (?spec::Spec, Typed a, Show a) => a -> [Expr] -> Expr
plusmod ar es = (plus $ map (exprPad w) es) .% EConst (UIntVal (bitWidth l) $ fromIntegral l)
    where Array _ l = typ ar
          w = bitWidth (l-1)

exprPad :: (?spec::Spec) => Int -> Expr -> Expr
exprPad w e | typeWidth e >= w = e
            | otherwise        = econcat [e, EConst $ UIntVal (w - typeWidth e) 0]

-- TODO: merge adjacent expressions
econcat :: [Expr] -> Expr
econcat [e]        = e
econcat (e1:e2:es) = econcat $ (EBinOp BConcat e1 e2):es

true = EConst $ BoolVal True
false = EConst $ BoolVal False

-- Subexpressions dereferenced inside the expression
exprPtrSubexpr :: Expr -> [Expr]
exprPtrSubexpr (EField e _)     = exprPtrSubexpr e
exprPtrSubexpr (EIndex a i)     = exprPtrSubexpr a ++ exprPtrSubexpr i
exprPtrSubexpr (ERange a (f,l)) = exprPtrSubexpr a ++ exprPtrSubexpr f ++ exprPtrSubexpr l
exprPtrSubexpr (ELength a)      = exprPtrSubexpr a
exprPtrSubexpr (EUnOp Deref e)  = e:(exprPtrSubexpr e)
exprPtrSubexpr (EUnOp _ e)      = exprPtrSubexpr e
exprPtrSubexpr (EBinOp _ e1 e2) = exprPtrSubexpr e1 ++ exprPtrSubexpr e2
exprPtrSubexpr (ESlice e _)     = exprPtrSubexpr e
exprPtrSubexpr (ERel _ as)      = concatMap exprPtrSubexpr as
exprPtrSubexpr _                = []

isConstExpr :: Expr -> Bool
isConstExpr (EVar _)         = False
isConstExpr (EConst _)       = True
isConstExpr (EField e _)     = isConstExpr e
isConstExpr (EIndex a i)     = isConstExpr a && isConstExpr i
isConstExpr (ERange a (f,l)) = all isConstExpr [a,f,l]
isConstExpr (ELength _)      = False
isConstExpr (EUnOp AddrOf e) = isConstLExpr e
isConstExpr (EUnOp _ e)      = isConstExpr e
isConstExpr (EBinOp _ e1 e2) = isConstExpr e1 && isConstExpr e2
isConstExpr (ESlice e _)     = isConstExpr e
isConstExpr (ERel _ _)       = False -- even if all args are constant, it may not evaluate to a constant

isConstLExpr :: Expr -> Bool
isConstLExpr (EVar _)     = True
isConstLExpr (EField s _) = isConstLExpr s
isConstLExpr (EIndex a i) = isConstLExpr a && isConstExpr i

evalConstExpr :: Expr -> Val
evalConstExpr (EConst v)                         = v
evalConstExpr (EUnOp op e) | isArithUOp op       = case s of
                                                        True  -> SIntVal w v
                                                        False -> UIntVal w v
                                                   where val     = evalConstExpr e
                                                         (v,s,w) = arithUOp op (ivalVal val,ivalIsSigned val,ivalWidth val)
evalConstExpr (EUnOp Not e)                      = BoolVal $ not b
                                                   where BoolVal b = evalConstExpr e
evalConstExpr (EUnOp AddrOf e)                   = PtrVal $ evalLExpr e
evalConstExpr (EBinOp op e1 e2) | isArithBOp op  = case s of
                                                        True  -> SIntVal w v
                                                        False -> UIntVal w v
                                                   where val1    = evalConstExpr e1
                                                         val2    = evalConstExpr e2
                                                         (v,s,w) = arithBOp op (ivalVal val1, ivalIsSigned val1, ivalWidth val1)
                                                                               (ivalVal val2, ivalIsSigned val2, ivalWidth val2)
evalConstExpr (EBinOp op e1 e2) | elem op [Eq,Neq,Lt,Gt,Lte,Gte,And,Or,Imp] = 
                                                   case v1 of
                                                        BoolVal _ -> case op of
                                                                          Eq  -> BoolVal $ b1 == b2
                                                                          Neq -> BoolVal $ b1 /= b2
                                                                          And -> BoolVal $ b1 && b2
                                                                          Or  -> BoolVal $ b1 || b2
                                                                          Imp -> BoolVal $ (not b1) || b2
                                                        EnumVal _ -> case op of
                                                                          Eq  -> BoolVal $ en1 == en2
                                                                          Neq -> BoolVal $ en1 /= en2
                                                        _         -> case op of
                                                                          Eq  -> BoolVal $ i1 == i2
                                                                          Neq -> BoolVal $ i1 /= i2
                                                                          Lt  -> BoolVal $ i1 < i2
                                                                          Gt  -> BoolVal $ i1 > i2
                                                                          Lte -> BoolVal $ i1 <= i2
                                                                          Gte -> BoolVal $ i1 >= i2
                                                   where v1 = evalConstExpr e1
                                                         v2 = evalConstExpr e2
                                                         BoolVal b1  = v1
                                                         BoolVal b2  = v2
                                                         EnumVal en1 = v1
                                                         EnumVal en2 = v2
                                                         i1 = ivalVal v1
                                                         i2 = ivalVal v2
evalConstExpr (ESlice e s)     = valSlice (evalConstExpr e) s

evalLExpr :: Expr -> LVal
evalLExpr (EVar n)     = LVar n
evalLExpr (EField s f) = LField (evalLExpr s) f
evalLExpr (EIndex a i) = LIndex (evalLExpr a) (ivalVal $ evalConstExpr i)

isMemExpr :: (?spec::Spec) => Expr -> Bool
isMemExpr (EVar n)     = varMem $ getVar n
isMemExpr (EField s _) = isMemExpr s
isMemExpr (EIndex a _) = isMemExpr a
isMemExpr (ERange a _) = isMemExpr a
isMemExpr (ESlice e _) = isMemExpr e
isMemExpr _            = False

mapExpr :: (Expr -> Expr) -> Expr -> Expr
mapExpr f e0 = case f e0 of
                    e@(EVar _)      -> e
                    e@(EConst _)    -> e
                    EField e n      -> EField (mapExpr f e) n
                    EIndex a i      -> EIndex (mapExpr f a) (mapExpr f i)
                    ERange a (fr,l) -> ERange (mapExpr f a) (mapExpr f fr, mapExpr f l)
                    ELength a       -> ELength (mapExpr f a)
                    EUnOp op e      -> EUnOp op (mapExpr f e)
                    EBinOp op e1 e2 -> EBinOp op (mapExpr f e1) (mapExpr f e2)
                    ESlice e s      -> ESlice (mapExpr f e) s
                    ERel n as       -> ERel n $ map (mapExpr f) as
