{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module ExprOps(evalInt) where

import Control.Monad.Error

import Scope
import Expr
import Spec

evalInt :: (?spec::Spec) => Scope -> ConstExpr -> Integer
evalInt = error "evalInt not implemented"

exprType :: (?spec::Spec, ?scope::Scope) => Expr -> (TypeSpec, Scope)
exprType (ETerm   _ n)           = (typ o, scope o) where o = scopeGetTerm ?scope n
exprType (ELit    p w True _ _)  = (SIntSpec p w,?scope)
exprType (ELit    p w False _ _) = (UIntSpec p w,?scope)
exprType (EBool   p _)           = (BoolSpec p  ,?scope)
exprType (EApply  _ m _)         = mapFst methRettyp $ scopeGetMethod ?scope m
exprType (EField  _ e f)         = (typ $ objGet (ObjType s t) f, s) where (t,s) = expandType ?scope $ exprType e
exprType (EPField _ e f)         = (typ $ objGet (ObjType s t) f, s) where (PtrSpec _ t,s) = expandType ?scope $ exprType e
exprType (EIndex _ e i)          = (t,s) where (ArraySpec _ t _,s) = expandType ?scope $ exprType e

          | EIndex  {epos::Pos, arr::Expr, idx::Expr}
          | EUnOp   {epos::Pos, uop::UOp, arg1::Expr}
          | EBinOp  {epos::Pos, bop::BOp, arg1::Expr, arg2::Expr}
          | ETernOp {epos::Pos, arg1::Expr, arg2::Expr, arg3::Expr}
          | ECase   {epos::Pos, caseexpr::Expr, cases::[(Expr, Expr)], def::(Maybe Expr)}
          | ECond   {epos::Pos, cases::[(Expr, Expr)], def::(Maybe Expr)}
          | ESlice  {epos::Pos, slexpr::Expr, slice::Slice}
          | EStruct {epos::Pos, typename::StaticSym, fields::(Either [(Ident, Expr)] [Expr])} -- either named or anonymous list of fields
          | ENonDet {epos::Pos}


-- Assumes that expression has been validated first
instance (?spec::Spec, ?scope::Scope) => WithType Expr where


-- Validating expressions
-- * case: 
--    - all components are valid expressions
--    - case conditions must type-match the case expression (should they be statically computable?)
--    - value expressions must match the type of the key expression
-- * cond: 
--    - condition expressions are valid boolean expressions
--    - value expressions have compatible types
-- * slice: 
--    - applied to an integer (unsigned?) value; 
--    - lower and upper bounds are constant expressions
--    - 0 <= lower bound <= upper bound <= type width - 1
-- * struct:
--    - typename refers to a struct type
--    - correct number and types of fields


validateExpr :: (?spec::Spec, MonadError String me) => Scope -> Expr -> me ()
validateExpr s e = let ?scope = s 
                   in validateExpr' e

-- * terms refer to variable or constants visible in the current scope
validateExpr' (ETerm _ n)        = do {scopeCheckTerm s n; return ()}
validateExpr' (ELit _ w r v)     = return ()
validateExpr' (EBool _ _)        = return ()

-- * method application:
--   - method name refers to a visible method (local or exported)
--   - the number and types of arguments match
validateExpr' (EApply p mref as) = do
    m <- scopeCheckMethod s mref
    assert ((length $ methArg m) == length as) p $
           "Method " ++ sname m ++ " takes " ++ show (length $ methArg m) ++ 
           " arguments, but is invoked with " ++ show (length as) ++ " arguments"
    mapM (\(marg,a) -> do validateExpr' a
                          assert (typeMatch marg a) (pos a) $
                                 "Argument type " ++ show (typ a) ++ " does not match expected type " ++ show (typ marg))
         (zip (methArg m) as)

-- * field selection refers to a valid struct field, or a valid and externally 
--   visible template variable, port or instance
validateExpr' (EField p e f) = do
    validateExpr' e
    case typ' ?scope e of
         StructSpec _ fs      -> assert (any ((==f) . name) fs) (pos f) $ "Unknown field name " ++ show f
         TemplateTypeSpec _ t -> case objLookup (ObjTemplate t) f of
                                      Nothing              -> err (pos f) $ "Unknown identifier " ++ show f
                                      Just (ObjPort     _) -> return ()
                                      Just (ObjInstance _) -> return ()
                                      Just (ObjGVar     v) -> assert (gvarExport v) (pos f) $
                                                                     "Cannot access private variable " ++ sname v ++ " of template " ++ show t
                                      _                    -> show f ++ " does not refer to an externally visible member of template " ++ show t
         _                    -> err (pos f) $ "Expression " ++ show s ++ " is not a struct or template"

validateExpr' (EPField p e f) = do
    validateExpr' e
    case flattenType ?scope e of
         PtrSpec _ (StructSpec _ fs) -> assert (any ((==f) . name) fs) (pos f) $ "Unknown field name " ++ show f
         _                           -> err (pos f) $ "Expression " ++ show s ++ " is not a struct pointer"


-- * index[]: applied to an array type expression; index value is a valid 
--   integral expression 
validateExpr' (EIndex _ a i) = do
    validateExpr' a
    validateExpr' i
    assert (isInt i) (pos i) $ show i ++ " is not of integral type"
    assert (isArray a) (pos i) $ show a ++ " is not an array"

validateExpr' (EUnOp p UMinus e) = do
    validateExpr' e
    assert (isInt e) p $ "Unary minus applied to expression " ++ show e ++ " of non-integral type"

validateExpr' (EUnOp p UNot e) = do
    validateExpr' e
    assert (isBool e) p $ "Logical negation applied to expression " ++ show e ++ " of non-boolean type"

validateExpr' (EUnOp p BNeg e) = do
    validateExpr' e
    assert (isInt e) p $ "Bit-wise negation applied to expression " ++ show e ++ " of non-integral type"

validateExpr' (EUnOp p Deref e) = do
    validateExpr' e
    assert (isPtr e) p $ "Cannot dereference non-pointer expression " ++ show e

validateExpr' (EUnOp p AddrOf e) = do
    validateExpr' e
    assert (isLExpr e) p $ "Cannot take address of expression " ++ show e ++ ", which is not an L-value"

validateExpr' (EBool p op e1 e2) = do
    validateExpr' e1
    validateExpr' e2
    if elem op [Eq,Neq]
      then assert (typesComparable e1 e2) p $ "Operator " ++ show op ++ " applied to expressions " ++ show e1 ++ 
                                              " and " ++ show e2 ++ " that have uncomparable types"
      else return () 
    if elem op [Lt,Gt,Lte,Gte,BinMinus,BAnd,BOr,BXor,Mod,Mul]
       then do assert (isInt e1) p $ "First operand " ++ show e1 ++ " of " ++ show op ++ " is of non-integral type"
               assert (isInt e2) p $ "Second operand " ++ show e2 ++ " of " ++ show op ++ " is of non-integral type"
       else return ()
    if elem op [And,Or,Imp]
       then do assert (isBool e1) p $ "First operand " ++ show e1 ++ " of " ++ show op ++ " is of non-boolean type"
               assert (isBool e2) p $ "Second operand " ++ show e2 ++ " of " ++ show op ++ " is of non-boolean type"
       else return ()
    if elem op [BAnd, BOr, BXor]
       then assert ((intTypeWidth $ typ' ?scope e1) == (intTypeWidth $ typ' ?scope e2)) p $ 
                   "Binary bitwise operator " ++ show op ++ " applied to arguments of different width: " ++
                   show e1 ++ " has width " ++ (show $ intTypeWidth $ typ' ?scope e1) ++ ", " ++ 
                   show e2 ++ " has width " ++ (show $ intTypeWidth $ typ' ?scope e2)
       else return ()

--ETernOp {epos::Pos, arg1::Expr, arg2::Expr, arg3::Expr}
--ECase   {epos::Pos, caseexpr::Expr, cases::[(Expr, Expr)], def::(Maybe Expr)}
--ECond   {epos::Pos, cases::[(Expr, Expr)], def::(Maybe Expr)}
--ESlice  {epos::Pos, slexpr::Expr, slice::Slice}
--EStruct {epos::Pos, typename::StaticSym, fields::(Either [(Ident, Expr)] [Expr])} -- either named or anonymous list of fields
--ENonDet {epos::Pos}
