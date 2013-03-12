{-# LANGUAGE ImplicitParams #-}

module Store (Store(..),
              storeUnion,
              storeUnions,
              storeProject,
              storeTryEval,
              storeEval,
              storeEvalScalar,
              storeEvalEnum,
              storeEvalBool,
              storeSet) where

import Data.List
import Control.Monad
import qualified Data.Map as M

import Ops
import IExpr


-- Variable assignments
data Store = SStruct {storeFields :: M.Map String Store} -- name/value pairs (used for structs and for top-level store)
           | SArr    {storeArr    :: M.Map Int Store}    -- array assignment
           | SVal    {storeVal    :: Val}                -- scalar

instance Show Store where
    show (SStruct fs) = "{" ++
                        (intercalate ", "
                         $ map (\(n, val) -> show n ++ "=" ++ show val)
                         $ M.toList fs) ++
                        "}"
    show (SArr ar)    = "[" ++
                        (intercalate ", "
                         $ map (\(idx, val) -> show idx ++ ": " ++ show val)
                         $ sortBy (\x y -> compare (fst x) (fst y)) 
                         $ M.toList ar) ++
                        "]"
    show (SVal v)     = show v

-- shallow union of stores
storeUnion :: Store -> Store -> Store
storeUnion (SStruct entries1) (SStruct entries2) = SStruct $ M.union entries1 entries2

storeUnions :: [Store] -> Store
storeUnions stores = foldl' storeUnion (SStruct M.empty) stores

-- project store on a subset of variables
storeProject :: Store -> [String] -> Store
storeProject (SStruct entries) names = SStruct $ M.filterWithKey (\n _ -> elem n names) entries

-- Expression evaluation over stores
storeTryEval :: Store -> Expr -> Maybe Store
storeTryEval (SStruct fs) (EVar name)       = M.lookup name fs
storeTryEval _            (EVar _)          = Nothing
storeTryEval _            (EConst v)        = Just $ SVal v
storeTryEval s            (EField e name)   = join $ fmap (M.lookup name) $ storeTryEvalStruct s e
storeTryEval s            (EIndex e i)      = do idx <- liftM fromInteger $ storeTryEvalInt s i
                                                 es  <- storeTryEvalArr s e
                                                 M.lookup idx es
storeTryEval s            (EUnOp op e)      = fmap (SVal . evalConstExpr . EUnOp op . EConst) $ storeTryEvalScalar s e
storeTryEval s            (EBinOp op e1 e2) = do v1 <- storeTryEvalScalar s e1
                                                 v2 <- storeTryEvalScalar s e2
                                                 return $ SVal $ evalConstExpr (EBinOp op (EConst v1) (EConst v2))
storeTryEval s            (ESlice e sl)     = fmap (\v -> SVal $ evalConstExpr (ESlice (EConst v) sl)) $ storeTryEvalScalar s e

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
                         Nothing -> error "storeEval: invalid expression"
                         Just s  -> s

storeEvalScalar :: Store -> Expr -> Val
storeEvalScalar s e = case storeTryEvalScalar s e of
                           Just v -> v
                           _      -> error "storeEvalScalar: invalid expression"

storeEvalBool :: Store -> Expr -> Bool
storeEvalBool store e = case storeTryEvalBool store e of
                             Nothing -> error "storeEvalBool: invalid expression"
                             Just b  -> b

storeEvalInt :: Store -> Expr -> Integer
storeEvalInt store e = case storeTryEvalInt store e of
                            Nothing -> error "storeEvalInt: invalid expression"
                            Just i  -> i

storeEvalEnum :: Store -> Expr -> String
storeEvalEnum store e = case storeTryEvalEnum store e of
                             Nothing -> error "storeEvalEnum: invalid expression"
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
storeSet' (SStruct fs) (EVar vname) Nothing  = SStruct $ M.delete vname fs
storeSet' (SStruct fs) (EVar vname) (Just v) = SStruct $ M.insert vname v fs
storeSet' s            (EField e n) val      = storeSet' s e $ case storeTryEval s e of
                                                                    Nothing -> Just $ storeSet' (SStruct M.empty) (EVar n) val
                                                                    Just s' -> Just $ storeSet' s'                (EVar n) val
storeSet' s            (EIndex a i) val      = storeSet' s a $ case (storeTryEval s a, val) of
                                                                    (Nothing, Nothing)        -> Nothing
                                                                    (Nothing, Just v)         -> Just $ SArr $ M.singleton idx v
                                                                    (Just (SArr es), Nothing) -> Just $ SArr $ M.delete idx es
                                                                    (Just (SArr es), Just v)  -> Just $ SArr $ M.insert idx v es
                                               where idx = fromInteger $ storeEvalInt ?store i
storeSet' s            (EUnOp Deref e) val   = storeSet' s (lvalToExpr l) val
                                               where PtrVal l = storeEvalScalar ?store e
storeSet' _            e               _     = error $ "storeSet': " ++ show e
