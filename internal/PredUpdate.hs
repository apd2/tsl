{-# LANGUAGE ImplicitParams #-}

module PredUpdate() where

import Data.Maybe
import Data.Functor
import Data.List
import Control.Applicative

import TSLUtil
import Predicate
import Cascade
import Formula
import ISpec
import Common

-- Predicate database
type PredicateDB = [Predicate]

pdbPtrPreds :: (?pdb::PredicateDB) => Expr -> [(Predicate, Term)]
pdbPtrPreds e = 
    mapMaybe (\p@(PAtom _ t1 t2) -> if t1 == t
                                       then case t2 of
                                                 TAddr t' -> Just (p,t')
                                                 _        -> Nothing
                                       else if t2 == t
                                               then case t1 of
                                                         TAddr t' -> Just (p,t')
                                                         _        -> Nothing
                                               else Nothing) 
             ?pdb
    where t = exprToTerm e

-- Expand each pointer dereference operation in the expression
-- using predicates in the DB.
exprExpandPtr :: (?pdb::PredicateDB) => Expr -> ECascade
exprExpandPtr e@(EVar _)          = CasLeaf e
exprExpandPtr e@(EConst _)        = CasLeaf e
exprExpandPtr   (EField e f)      = fmap (\e -> EField e f) $ exprExpandPtr e
exprExpandPtr   (EIndex a i)      = EIndex <$> exprExpandPtr a <*> exprExpandPtr i
exprExpandPtr   (EUnOp Deref e)   = casMap (CasTree . (map (\(p, t) -> (FPred p, CasLeaf $ termToExpr t))) . pdbPtrPreds)
                                           $ exprExpandPtr e
exprExpandPtr   (EBinOp op e1 e2) = (EBinOp op) <$> exprExpandPtr e1 <*> exprExpandPtr e2
exprExpandPtr   (ESlice e s)      = fmap (\e -> ESlice e s) $ exprExpandPtr e


combineExpr :: (?spec::Spec) => RelOp -> Expr -> Expr -> Formula
combineExpr op e1 e2 | typ e1 == Bool =
   case e1 of
       EConst (BoolVal True)  -> if op == REq then exprToFormula' e2 else FNot $ exprToFormula' e2
       EConst (BoolVal False) -> if op == REq then FNot $ exprToFormula' e2 else exprToFormula' e2
       _                      -> 
           case e2 of
                EConst (BoolVal True)  -> if op == REq then exprToFormula' e1 else FNot $ exprToFormula' e1
                EConst (BoolVal False) -> if op == REq then FNot $ exprToFormula' e1 else exprToFormula' e1
                _                      -> let f = FBinOp Equiv (exprToFormula' e1) (exprToFormula' e2)
                                          in if op == REq then f else FNot f
                     | otherwise      = FPred $ pAtom op (exprToTerm e1) (exprToTerm e2)

-- Convert boolean expression without pointers to a formula
exprToFormula' :: Expr -> Formula
exprToFormula' e@(EVar n)                         = FPred $ pAtom (exprToTerm e) TTrue
exprToFormula'   (EConst (BoolVal True))          = FTrue
exprToFormula'   (EConst (BoolVal False))         = FFalse
exprToFormula' e@(EField s f)                     = FPred $ pAtom (exprToTerm e) TTrue
exprToFormula' e@(EIndex a i)                     = FPred $ pAtom (exprToTerm e) TTrue
exprToFormula'   (EUnOp Not e)                    = FNot $ exprToFormula' e
exprToFormula'   (EBinOp op e1 e2) | isRelBOp op  = combineExpr (bopToRelOp op) e1 e2
exprToFormula'   (EBinOp op e1 e2) | isBoolBOp op = FBinOp (bopToBoolOp op) (exprToFormula' e1) (exprToFormula' e2)


exprToFormulaModified :: (?pdb::PredicateDB) => Expr -> Formula
exprToFormulaModified e = error "Not implemented: exprToFormulaModified" -- consider special case *x==y

-- Convert boolean expression (possibly with pointers) to a formula
exprToFormula :: (?pdb::PredicateDB) => Expr -> Formula
exprToFormula e = fcasToFormula $ fmap exprToFormula' $ exprExpandPtr e

-- Weakest precondition of a formula wrt a statement
updateFormStat :: (?spec::Spec) => Formula -> Statement -> Formula
updateFormStat f (SAssume e)     = FBinOp Conj f (exprToFormula e)
updateFormStat f (SAssign e1 e2) = foldl' (\f (e1,e2) -> updateFormAsn e1 e2 f) f $ zip sc1 sc2
    where sc1 = scalars e1 (typ e1)
          sc2 = scalars e2 (typ e2)

-- Formula update by assignment statement
updateFormAsn :: Expr -> Expr -> Formula -> Formula
updateFormAsn lhs rhs f = 
    foldl' (\f p -> FReplace f p (updatePredAsn lhs rhs p)) f $ formPreds f

-- Predicate update by assignment statement
updatePredAsn :: Expr -> Expr -> Predicate -> Formula
updatePredAsn lhs rhs p = pSubstScalCas p sc'
    where sc' = map (updateScalAsn lhs rhs) $ pScalars p
 
-- Takes lhs and rhs of assignment statement and a term
-- Computes possible overlaps of the lhs with the term and
-- corresponding next-state values of the term expressed as concatenation 
-- of slices of the rhs and the original term.
updateScalAsn :: Expr -> Expr -> Term -> ECascade
updateScalAsn e                rhs (TSlice t s) = casSlice (updateScalAsn e rhs t) s
updateScalAsn (ESlice e (l,h)) rhs t            = 
    fmap (\b -> if b
                   then tConcat $
                        (if l == 0 then [] else [termToExpr $ TSlice t (0,l-1)] ++
                        [ESlice rhs (l,h)] ++
                        if h == w - 1 then [] else [termToExpr $ TSlice t (h+1, w - 1)])
                   else termToExpr t) 
         $ lhsTermEq e t
    where w = exprWidth e
updateScalAsn lhs              rhs t            = 
    fmap (\b -> if b then rhs else termToExpr t) $ lhsTermEq lhs t


-- Takes lhs expression and a term and computes the condition 
-- when the expression is a synonym of the term.
lhsTermEq :: Expr -> Term -> ECascade
lhsTermEq (EVar n1)       (TVar n2)        | n1 == n2 = CasLeaf True
lhsTermEq (EField e f1)   (TField t f2)    | f1 == f2 = lhsTermEq e t
lhsTermEq (EIndex ae ie)  (TIndex at it)              = 
    casMap (\b -> if b 
                     then case exprToFormula $ (termToExpr it) === ie of
                               FTrue  -> CasLeaf True
                               FFalse -> CasLeaf False
                               f      -> CasTree [(f, CasLeaf True), (FNot f, CasLeaf False)]
                     else CasLeaf False)
           $ lhsTermEq ae at
lhsTermEq (EUnOp Deref e) t                 | typeMatch etyp ttyp && isMemTerm t = 
    case exprToFormula $ e === EUnOp AddrOf (termToExpr t) of
         FTrue  -> CasLeaf True
         FFalse -> CasLeaf False
         f      -> CasTree [(f, CasLeaf True), (FNot f, CasLeaf False)]
    where Ptr etyp = typ e
          ttyp     = typ t
lhsTermEq _              _                            = CasLeaf False


-- Extract scalar variables terms from predicate
pScalars :: Predicate -> [Term]
pScalars (PAtom op t1 t2) = tScalars t1 ++ tScalars t2

tScalars :: Term -> [Term]
tScalars t@(TVar   _)           = [t]
tScalars   (TInt   _)           = []
tScalars   (TEnum  _)           = []
tScalars   (TTrue  _)           = []
tScalars   (TAddr (TVar _))     = []                    -- address of a variable is a constant
tScalars   (TAddr (TField s _)) = tScalars (TAddr s)    -- address of a field has the same set of scalars as address of the struct
tScalars   (TAddr (TIndex a i)) = tScalars (TAddr a) ++ -- address of array element has the same scalars as address of the array
                                  tScalars i            --   plus scalars in the index expression
tScalars t@(TField _ _)     = [t]
tScalars t@(TIndex _ _)     = [t]
tScalars   (TUnOp  _ t)     = tScalars t
tScalars   (TBinOp _ t1 t2) = tScalars t1 ++ tScalars t2
tScalars   (TSlice t _)     = tScalars t

-- Substitute all scalar terms in a predicate with cascades of scalar expressions.
-- The order of cascades is assumed to be the same one returned by pScalars.
pSubstScalCas :: Predicate -> [ECascade] -> Formula
pSubstScalCas (PAtom op t1 t2) cas = (\e1 e2 -> exprToFormulaModified $ EBinOp (relOpToBOp op) e1 e2) <$> t1' <*> t2'
    where (t1', cas') = tSubstCas t1 cas
          (t2', _   ) = tSubstCas t2 cas'

tSubstCas :: Term -> [ECascade] -> (ECascade, [ECascade])
tSubstCas   (TVar   _)           cas = (head cas              , tail cas)
tSubstCas t@(TInt   _)           cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TEnum  _)           cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TTrue  _)           cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TAddr (TVar _))     cas = (CasLeaf $ termToExpr t, cas)
tSubstCas   (TAddr (TField s f)) cas = mapFst (fmap (\(EUnOp AddrOf e) -> EUnOp AddrOf (EField e f))) 
                                              $ tSubstCas (TAddr s)
tSubstCas   (TAddr (TIndex a i)) cas = let (a', cas1) = mapFst (fmap (\(EUnOp AddrOf e) -> EUnOp AddrOf (EField e f))) 
                                                               $ tSubstCas (TAddr a)
                                           (i', cas2) = tSubstCas i cas'
                                       in ((\a i -> CasLeaf $ EIndex a i) <$> a' <*> i', cas2)
tSubstCas   (TField _ _)         cas = (head cas              , tail cas)
tSubstCas   (TIndex _ _)         cas = (head cas              , tail cas)
tSubstCas   (TUnOp  op t)        cas = mapFst (fmap (\e -> EUnOp (arithOpToUOp op) e)) $ tSubstCas t
tSubstCas   (TBinOp op t1 t2)    cas = let (t1', cas1) = tSubstCas t1 cas
                                           (t2', cas2) = tSubstCas t2 cas1
                                       in ((\e1 e2 -> EBinOp (arithOpToBOp op) e1 e2) <$> t1' <*> t2', cas2)
tSubstCas   (TSlice t s)         cas = mapFst (fmap (\e -> eSlice e s)) $ tSubstCas t
