{-# LANGUAGE ImplicitParams #-}

module Store (Store(..),
              storeUnion,
              storeUnions,
              storeProject,
              storeTryEval,
              storeEval,
              storeTryEvalScalar,
              storeEvalScalar,
              storeTryEvalEnum,
              storeEvalEnum,
              storeTryEvalBool,
              storeEvalBool,
              storeSet,
              storeExtendDefault,
              storeExtendDefaultState,
              storeExtendDefaultLabel) where

import Data.List
import Data.Maybe
import Control.Monad
import qualified Data.Map as M
import Debug.Trace

import Util hiding(trace)
import Ops
import IExpr
import IVar
import IType
import ISpec
import IRelation
import {-# SOURCE #-} AbsRelation

-- Variable assignments
data Store = SStruct {storeFields :: M.Map String Store, storeSpec :: Spec} -- name/value pairs (used for structs and for top-level store)
           | SArr    {storeArr    :: M.Map Int Store}                       -- array assignment
           | SVal    {storeVal    :: Val}                                   -- scalar

instance Eq Store where
    (SStruct fs1 _ ) == (SStruct fs2 _) = fs1 == fs2
    (SArr a1)        == (SArr a2)       = a1  == a2
    (SVal v1)        == (SVal v2)       = v1  == v2

isScalarStore :: Store -> Bool
isScalarStore (SVal _) = True
isScalarStore _        = False

instance Show Store where
    show (SStruct fs _) = "{" ++
                          (intercalate ", "
                           $ map (\(n, val) -> show n ++ "=" ++ show val)
                           $ M.toList fs) ++
                          "}"
    show (SArr ar)      = "[" ++
                          (intercalate ", "
                           $ map (\(idx, val) -> show idx ++ ": " ++ show val)
                           $ sortBy (\x y -> compare (fst x) (fst y)) 
                           $ M.toList ar) ++
                          "]"
    show (SVal v)       = show v

-- shallow union of stores
storeUnion :: Store -> Store -> Store
storeUnion (SStruct entries1 spec) (SStruct entries2 _) = SStruct (M.union entries1 entries2) spec

storeUnions :: Spec -> [Store] -> Store
storeUnions spec stores = foldl' storeUnion (SStruct M.empty spec) stores

-- project store on a subset of variables
storeProject :: Store -> [String] -> Store
storeProject (SStruct entries spec) names = SStruct (M.filterWithKey (\n _ -> elem n names) entries) spec

-- Expression evaluation over stores
storeTryEval :: Store -> Expr -> Maybe Store
storeTryEval (SStruct fs _) (EVar name)        = M.lookup name fs
storeTryEval _              (EVar _)           = Nothing
storeTryEval _              (EConst v)         = Just $ SVal v
storeTryEval s              (EField e name)    = join $ fmap (M.lookup name) $ storeTryEvalStruct s e
storeTryEval s              (EIndex e i)       = do idx <- liftM fromInteger $ storeTryEvalInt s i
                                                    es  <- storeTryEvalArr s e
                                                    M.lookup idx es
storeTryEval s              (EUnOp op e)       = fmap (SVal . evalConstExpr . EUnOp op . EConst) $ storeTryEvalScalar s e
-- evluate =>, ||, && lazily
storeTryEval s              (EBinOp Imp e1 e2) = storeTryEval s (EBinOp Or (EUnOp Not e1) e2)
storeTryEval s              (EBinOp Or e1 e2)  = do b1 <- storeTryEvalBool s e1
                                                    if b1 
                                                       then return $ SVal $ BoolVal True
                                                       else do b2 <- storeTryEvalBool s e2
                                                               return $ SVal $ BoolVal b2
storeTryEval s              (EBinOp And e1 e2) = do b1 <- storeTryEvalBool s e1
                                                    if not b1 
                                                       then return $ SVal $ BoolVal False
                                                       else do b2 <- storeTryEvalBool s e2
                                                               return $ SVal $ BoolVal b2
storeTryEval s              (EBinOp op e1 e2)  = do s1 <- storeTryEval s e1
                                                    s2 <- storeTryEval s e2
                                                    if isScalarStore s1
                                                       then do let SVal v1 = s1
                                                                   SVal v2 = s2
                                                               return $ SVal $ evalConstExpr (EBinOp op (EConst v1) (EConst v2))
                                                       else return $ SVal $ BoolVal 
                                                                   $ case op of
                                                                          Eq  -> s1 == s2
                                                                          Neq -> s1 /= s2
storeTryEval s              (ESlice e sl)        = fmap (\v -> SVal $ evalConstExpr (ESlice (EConst v) sl)) $ storeTryEvalScalar s e
storeTryEval s@(SStruct _ sp) e@(ERel n as)      = trace ("storeTryEval " ++ show e) $
                                                   let ?spec = sp in 
                                                   let rel = getRelation n
                                                       rules = map snd $ filter ((== Implied) . fst) $ snd $ instantiateRelation rel as
                                                       rulevals = mapMaybe (storeTryEvalBool s) rules
                                                   in if' (null rulevals) Nothing (Just $ SVal $ BoolVal $ or rulevals)
                                                      

storeTryEvalScalar :: Store -> Expr -> Maybe Val
storeTryEvalScalar s e = fmap storeVal $ storeTryEval s e

storeTryEvalInt :: Store -> Expr -> Maybe Integer
storeTryEvalInt s e = fmap ivalVal $ storeTryEvalScalar s e

storeTryEvalBool :: Store -> Expr -> Maybe Bool
storeTryEvalBool s e = case storeTryEvalScalar s e of
                            Just (BoolVal b) -> Just b
                            _                -> Nothing

storeTryEvalEnum :: Store -> Expr -> Maybe String
storeTryEvalEnum s e = case storeTryEvalScalar s e of
                            Just (EnumVal n) -> Just n
                            _                -> Nothing

storeTryEvalStruct :: Store -> Expr -> Maybe (M.Map String Store) 
storeTryEvalStruct s e = fmap storeFields $ storeTryEval s e

storeTryEvalArr :: Store -> Expr -> Maybe (M.Map Int Store)
storeTryEvalArr s e = fmap storeArr $ storeTryEval s e

storeEval :: Store -> Expr -> Store
storeEval store e = case storeTryEval store e of
                         Nothing -> error $ "storeEval: invalid expression " ++ show e
                         Just s  -> s

storeEvalScalar :: Store -> Expr -> Val
storeEvalScalar s e = case storeTryEvalScalar s e of
                           Just v -> v
                           _      -> error $ "storeEvalScalar: invalid expression " ++ show e

storeEvalBool :: Store -> Expr -> Bool
storeEvalBool store e = case storeTryEvalBool store e of
                             Nothing -> error $ "storeEvalBool: invalid expression " ++ show e ++ 
                                                "\nStore: " ++ show store
                             Just b  -> b

storeEvalInt :: Store -> Expr -> Integer
storeEvalInt store e = case storeTryEvalInt store e of
                            Nothing -> error "storeEvalInt: invalid expression"
                            Just i  -> i

storeEvalEnum :: Store -> Expr -> String
storeEvalEnum store e = case storeTryEvalEnum store e of
                             Nothing -> error $ "storeEvalEnum: invalid expression " ++ show e ++
                                                "\nStore: " ++ show store
                             Just s  -> s

storeSet :: Store -> Expr -> Maybe Store -> Store
storeSet s (ESlice e (l,h)) (Just (SVal val)) = 
    let ?store = s in
    let old = storeEvalScalar s e
        new = evalConstExpr $ econcat $
              (if l > 0 then [EConst $ valSlice old (0, l-1)] else []) ++
              [EConst $ val] ++
              (if h < ivalWidth old - 1 then [EConst $ valSlice old (h+1, ivalWidth old - 1)] else []) in
    storeSet s e (Just $ SVal $ old {ivalVal = ivalVal new})

storeSet s e val = let ?store = s in storeSet' s e val

storeSet' :: (?store::Store) => Store -> Expr -> Maybe Store -> Store
storeSet' (SStruct fs sp)  (EVar vname) Nothing  = SStruct (M.delete vname fs)   sp
storeSet' (SStruct fs sp)  (EVar vname) (Just v) = SStruct (M.insert vname v fs) sp
storeSet' s@(SStruct _ sp) (EField e n) val      = storeSet' s e $ case storeTryEval s e of
                                                                        Nothing -> Just $ storeSet' (SStruct M.empty sp) (EVar n) val
                                                                        Just s' -> Just $ storeSet' s'                   (EVar n) val
storeSet' s                (EIndex a i) val      = storeSet' s a $ case (storeTryEval s a, val) of
                                                                        (Nothing, Nothing)        -> Nothing
                                                                        (Nothing, Just v)         -> Just $ SArr $ M.singleton idx v
                                                                        (Just (SArr es), Nothing) -> Just $ SArr $ M.delete idx es
                                                                        (Just (SArr es), Just v)  -> Just $ SArr $ M.insert idx v es
                                                   where idx = fromInteger $ storeEvalInt ?store i
storeSet' s               (EUnOp Deref e) val    = storeSet' s (lvalToExpr l) val
                                                   where PtrVal l = storeEvalScalar ?store e
storeSet' _               e               _      = error $ "storeSet': " ++ show e

-- Assign all unassigned state variables to their default values

storeExtendDefault :: (?spec::Spec) => Store -> [Var] -> Store
storeExtendDefault store vs = foldl' (\st v -> let evar = EVar $ varName v in
                                               foldl' extendScalar st (exprScalars evar (typ evar)))
                                     store vs

storeExtendDefaultState :: (?spec::Spec) => Store -> Store
storeExtendDefaultState store = storeExtendDefault store $ filter ((== VarState) . varCat) (specVar ?spec)

storeExtendDefaultLabel :: (?spec::Spec) => Store -> Store
storeExtendDefaultLabel store = storeExtendDefault store $ filter ((== VarTmp) . varCat) (specVar ?spec)

extendScalar :: (?spec::Spec) => Store -> Expr -> Store
extendScalar store e = case storeTryEval store e of
                            Nothing -> storeSet store e (Just $ SVal $ valDefault e)
                            _       -> store
