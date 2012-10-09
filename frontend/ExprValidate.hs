{-# LANGUAGE ImplicitParams, TupleSections, FlexibleContexts #-}

module ExprValidate(validateExpr, validateExpr',
                    validateCall) where

import Control.Monad.Error
import Data.Maybe

import TSLUtil
import Pos
import Name
import Type
import TypeOps
import NS
import Expr
import {-# SOURCE #-} ExprOps
import Method
import Spec
import Template

validateExpr :: (?spec::Spec, MonadError String me) => Scope -> Expr -> me ()
validateExpr s e = let ?scope = s 
                   in validateExpr' e

validateExpr' :: (?spec::Spec, ?scope::Scope, MonadError String me) => Expr -> me ()

-- * terms refer to variable or constants visible in the current scope
validateExpr' (ETerm _ n)        = do {checkTerm ?scope n; return ()}
validateExpr' (ELit _ _ _ _ _)   = return ()
validateExpr' (EBool _ _)        = return ()

-- * method application:
--   - method name refers to a visible method (local or exported)
--   - the number and types of arguments match
validateExpr' (EApply p mref as) = do
    validateCall p mref as
    let (_, m) = getMethod ?scope mref
    assert (isJust $ methRettyp m) p $ "Method " ++ sname m ++ " has void return type and cannot be used in expression"

-- * field selection refers to a valid struct field, or a valid and externally 
--   visible template variable, port or instance
validateExpr' (EField p e f) = do
    validateExpr' e
    case tspec $ typ' e of
         StructSpec _ fs      -> assert (any ((==f) . name) fs) (pos f) $ "Unknown field name " ++ show f
         TemplateTypeSpec _ t -> case objLookup (ObjTemplate (getTemplate t)) f of
                                      Nothing                -> err (pos f) $ "Unknown identifier " ++ show f
                                      Just (ObjPort   _ _)   -> return ()
                                      Just (ObjInstance _ _) -> return ()
                                      Just (ObjGVar   _ v)   -> assert (gvarExport v) (pos f) $
                                                                       "Cannot access private variable " ++ sname v ++ " of template " ++ show t
                                      Just (ObjWire   _ w)   -> assert (wireExport w) (pos f) $
                                                                       "Cannot access private wire " ++ sname w ++ " of template " ++ show t
                                      _                      -> err (pos f) $ show f ++ " does not refer to an externally visible member of template " ++ show t
         _                    -> err (pos f) $ "Expression " ++ show e ++ " is not a struct or template"

validateExpr' (EPField p e f) = do
    validateExpr' e
    case typ' e of
         (Type s (PtrSpec _ t)) -> case tspec $ typ' $ Type s t of
                                        StructSpec _ fs -> assert (any ((==f) . name) fs) (pos f) $ "Unknown field name " ++ show f
                                        _               -> err (pos f) $ "Expression " ++ show e ++ " is not a struct pointer"
         _                      -> err (pos f) $ "Expression " ++ show e ++ " is not a pointer"


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

validateExpr' (EUnOp p Not e) = do
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
    assert (isMemExpr e) p $ "Cannot take address of expression " ++ show e

validateExpr' (EBinOp p op e1 e2) = do
    validateExpr' e1
    validateExpr' e2
    if elem op [Eq,Neq]
      then assert (typeComparable e1 e2) p $ "Operator " ++ show op ++ " applied to expressions " ++ show e1 ++ 
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
       then assert (typeWidth e1 == typeWidth e2) p $ 
                   "Binary bitwise operator " ++ show op ++ " applied to arguments of different width: " ++
                   show e1 ++ " has width " ++ (show $ typeWidth e1) ++ ", " ++ 
                   show e2 ++ " has width " ++ (show $ typeWidth e2)
       else return ()

validateExpr' (ETernOp p e1 e2 e3) = do
    validateExpr' e1
    validateExpr' e2
    validateExpr' e3
    assert (isBool e1) (pos e1) $ "First operand " ++ show e1 ++ " of ?: is of non-boolean type"
    assert (typeMatch e2 e3) p $ "Arguments of ternary operator have incompatible types: " ++
                                 show e1 ++ " has type " ++ show (tspec e1) ++ ", " ++
                                 show e2 ++ " has type " ++ show (tspec e2)

-- * case: 
--    - case conditions must type-match the case expression (should they be statically computable?)
--    - value expressions and default expression must all have matching types
validateExpr' (ECase p e cs md) = do
    validateExpr' e
    assert (length cs > 0) p $ "Empty case expression"
    mapM (\(e1,e2) -> do validateExpr' e1
                         validateExpr' e2
                         assert (exprNoSideEffects e1) (pos e1) "Case label must be side-effect free")
         cs
    case md of
         Just d  -> validateExpr' d
         Nothing -> return ()
    mapM (\(e1,_) -> assert (typeComparable e e1) (pos e1) $ 
                     "Expression " ++ show e1 ++ " has type "  ++ (show $ tspec e1) ++ 
                     ", which does not match the type " ++ (show $ tspec e) ++ " of the key expression " ++ show e) cs
    let e1 = fst $ head cs
    mapM (\(_,e2) -> assert (typeMatch e1 e2) (pos e2) $ 
                            "Clauses of a case expression return values of incompatible types:\n  " ++ 
                            show e1 ++ "(" ++ spos e1 ++ ") has type " ++ (show $ tspec e1) ++ "\n  " ++
                            show e2 ++ "(" ++ spos e2 ++ ") has type " ++ (show $ tspec e2))
         ((tail cs) ++ (map (undefined,) $ maybeToList md))
    return ()
                      
-- * cond: 
--    - condition expressions are valid boolean expressions
--    - value expressions have compatible types
validateExpr' (ECond p cs md) = do
    assert (length cs > 0) p $ "Empty case expression"
    mapM (\(e1,e2) -> do validateExpr' e1
                         validateExpr' e2
                         assert (exprNoSideEffects e1) (pos e1) "Condition must be side-effect free"
                         assert (isBool e1) (pos e1) $ "Expression " ++ show e1 ++ " is of non-boolean type")
         cs
    case md of
         Just d  -> validateExpr' d
         Nothing -> return ()
    let e1 = fst $ head cs
    mapM (\(_,e2) -> assert (typeMatch e1 e2) (pos e2) $ 
                            "Clauses of a conditional expression return values of incompatible types:\n  " ++ 
                            show e1 ++ "(" ++ spos e1 ++ ") has type " ++ (show $ tspec e1) ++ "\n  " ++
                            show e2 ++ "(" ++ spos e2 ++ ") has type " ++ (show $ tspec e2))
         ((tail cs) ++ (map (undefined,) $ maybeToList md))
    return ()
    
-- * slice: 
--    - applied to an integer (unsigned?) value; 
--    - lower and upper bounds are constant expressions
--    - 0 <= lower bound <= upper bound <= type width - 1
validateExpr' (ESlice p e (l,h)) = do
    validateExpr' e
    validateExpr' l
    validateExpr' h
    assert (isInt e) (pos e)                $ "Cannot compute slice of a non-integer expression " ++ show e
    assert (isConstExpr l) (pos l)          $ "Lower bound " ++ show l ++ " of a slice is a non-constant expression"
    assert (isConstExpr h) (pos h)          $ "Upper bound " ++ show h ++ " of a slice is a non-constant expression"
    assert (0 <= evalInt l) (pos l)         $ "Lower bound " ++ show l ++ " of a slice has negative value " ++ (show $ evalInt l)
    assert (evalInt l <= evalInt h) (pos l) $ "Lower bound " ++ show l ++ "=" ++ (show $ evalInt l) ++ " of a slice is greater than " ++
                                              "upper bound " ++ show h ++ "=" ++ (show $ evalInt h) 
    let w = typeWidth e
    assert (evalInt h < fromIntegral w) (pos h) $ "Upper bound " ++ show h ++ "=" ++ (show $ evalInt h) ++ " of a slice " ++
                                                  "exceeds argument width (" ++ show w ++ ") bits"

-- * struct:
--    - typename refers to a struct type
--    - correct number and types of fields
validateExpr' (EStruct p n es) = do
    (d,s) <- checkTypeDecl ?scope n
    let t = Type s $ tspec d
    assert (isStruct t) (pos n) $ show n ++ " is not a struct type"
    let (StructSpec _ fs) = tspec d
        nes = case es of 
                   Left es -> length es
                   Right es -> length es
    assert (length fs == nes) p $ "struct " ++ sname d ++ " has " ++ show (length fs) ++ " members, but is instantiated with " ++  show nes ++ " members"
    case es of
         Left  es -> mapM (\(((n,e),f),id) -> do assert (n == name f) (pos n) $ 
                                                        "Incorrect field name: field " ++ show id ++ " of struct " ++ sname d ++ " has name " ++ show n
                                                 validateExpr' e
                                                 assert (typeComparable e $ Type s $ tspec f) (pos e) $ 
                                                        "Could not match expected type " ++ (show $ tspec f) ++ " with actual type " ++ (show $ tspec e) ++ " in expression " ++ show e)
                          (zip (zip es fs) [1..])
         Right es -> mapM (\((e,f),id) -> do validateExpr' e
                                             assert (typeComparable e $ Type s $ tspec f) (pos e) $ 
                                                    "Could not match expected type " ++ (show $ tspec f) ++ " with actual type " ++ (show $ tspec e) ++ " in expression " ++ show e)
                          (zip (zip es fs) [1..])
    return ()

validateExpr' (ENonDet _) = return ()

-- Common code to validate method calls in statement and expression contexts
validateCall :: (?spec::Spec, ?scope::Scope, MonadError String me) => Pos -> MethodRef -> [Expr] -> me ()
validateCall p mref as = do
    let isfunc = case ?scope of
                      ScopeMethod _ _ -> True
                      _               -> False
    (t,m) <- checkMethod ?scope mref
    assert ((length $ methArg m) == length as) p $
           "Method " ++ sname m ++ " takes " ++ show (length $ methArg m) ++ 
           " arguments, but is invoked with " ++ show (length as) ++ " arguments"
    assert ((not isfunc) || (methCat m == Function)) (pos mref) $ show (methCat m) ++ " invocation not allowed in function context"
    mapM (\(marg,a) -> do validateExpr' a
                          checkTypeMatch (ObjArg (ScopeMethod t m) marg) a
                          assert ((not isfunc) || exprNoSideEffects a) (pos a) $ "Expression " ++ show a ++ " has side effects "
                          if argDir marg == ArgOut
                             then do assert (isLExpr a) (pos a) $ "Expression " ++ show a ++ " is not an L-value"
                                     assert ((not isfunc) || (isLocalLHS a)) (pos a) $ "out argument " ++ sname marg ++ " of method " ++ 
                                                                                       sname m ++ " refers to non-local state"
                             else return ())
         (zip (methArg m) as)
    return ()
