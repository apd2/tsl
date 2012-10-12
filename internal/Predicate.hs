{-# LANGUAGE ImplicitParams #-}

module Predicate() where

import Common
import ISpec

-- Arithmetic operations
data ArithUOp = AUMinus 
              | ABNeg
              deriving (Eq)

uopToArithOp :: UOp -> ArithUOp
uopToArithOp UMinus = AUMinus
uopToArithOp BNeg   = ABNeg

arithOpToUOp :: ArithUOp -> UOp 
arithOpToUOp AUMinus = UMinus
arithOpToUOp ABNeg   = BNeg

data ArithBOp = ABAnd 
              | ABOr 
              | ABXor
              | ABConcat
              | APlus 
              | ABinMinus 
              | AMod
              | AMul
              deriving(Eq)

-- Arithmetic (scalar) term
data Term = TVar    String
          | TInt    Integer
          | TEnum   String
          | TTrue
          | TAddr   Term
          | TField  Term String
          | TIndex  Term Term
          | TUnOp   ArithUOp Term
          | TBinOp  ArithBOp Term Term
          | TSlice  Term (Int,Int)

-- Relational operations
data RelOp = REq
           | RNeq 
           | RLt 
           | RGt 
           | RLte 
           | RGte
           deriving (Eq)

bopToRelOp :: BOp -> RelOp
bopToRelOp Eq  = REq
bopToRelOp Neq = RNeq
bopToRelOp Lt  = RLt
bopToRelOp Gt  = RGt
bopToRelOp Lte = RLte
bopToRelOp Gte = RGte

relOpToBOp :: RelOp -> BOp
relOpToBOp REq  = Eq
relOpToBOp RNeq = Neq
relOpToBOp RLt  = Lt
relOpToBOp RGt  = Gt
relOpToBOp RLte = Lte
relOpToBOp RGte = Gte


-- Predicates
data Predicate = PAtom {pOp :: RelOp, p1 :: Term, p2 :: Term}

pAtom :: RelOp -> Term -> Term -> Predicate
pAtom op l r = norm $ PAtom op l r

-- Objects with canonical form
class Canonical a where
    norm :: a -> a

instance Canonical Predicate where

-- Predicate database
type PredicateDB = [Predicate]

-- Logical operations
data BoolOp = Conj 
            | Disj 
            | Impl
            | Equiv
            deriving (Eq)

-- Formula consists of predicates and boolean constants
-- connected with boolean connectors
data Formula = FTrue
             | FFalse
             | FPred    Predicate
             | FBinOp   BoolOp Formula Formula
             | FNot     Formula
             | FReplace Formula Predicate Formula

-- Intermediate data structure that represents the value of
-- an arithmetic expression depending on pointer predicates
-- or other conditions
data Cascade a = CasTree  [(Formula, Cascade a)] 
               | CasLeaf a

ctrue :: Cascade Expr
ctrue = CasLeaf true

pdbPtrPreds :: Expr -> [(Predicate, Expr)]

-- Expand each pointer dereference operation in the expression
-- using predicates in the DB.
exprExpandPtr :: (?pdb::PredicateDB) => Expr -> Cascade Expr
exprExpandPtr e@(EVar _)             = CasLeaf e
exprExpandPtr e@(EConst _)           = CasLeaf e
exprExpandPtr   (EField e f)         = casMap (\e -> CasLeaf $ EField e f) $ exprExpandPtr e
exprExpandPtr   (EIndex a i)         = EIndex <$> exprExpandPtr a <*> exprExpandPtr i
exprExpandPtr   (EUnOp Deref e)      = casMap (CasTree . 
                                               (\ps -> map (\(p, lexpr) -> (FPred p, CasLeaf lexpr)) ps) . 
                                               pdbPtrPreds)
                                              $ exprExpandPtr e
exprExpandPtr   (EBinOp op e1 e2)    = (EBinOp op) <$> exprExpandPtr e1 <*> exprExpandPtr e2
exprExpandPtr   (ESlice e s)         = casMap (\e -> CasLeaf $ ESlice e s) $ exprExpandPtr e


-- Compare two cascades
combine :: RelOp -> Cascade Expr -> Cascade Expr -> Formula
combine op c1 c2 = casToFormula $ (combineExpr op) <$> c1 <*> c2

combineExpr :: RelOp -> Expr -> Expr -> Formula
combineExpr op e1 e2 | typ e1 == Bool =
   case e1 of
       EConst (BoolVal True)  -> if op == REq then boolExprToFormula e2 else FNot $ boolExprToFormula e2
       EConst (BoolVal False) -> if op == REq then FNot $ boolExprToFormula e2 else boolExprToFormula e2
       _                      -> 
           case e2 of
                EConst (BoolVal True)  -> if op == REq then boolExprToFormula e1 else FNot $ boolExprToFormula e1
                EConst (BoolVal False) -> if op == REq then FNot $ boolExprToFormula e1 else boolExprToFormula e1
                _                      -> let f = FBinOp Equiv (boolExprToFormula e1) (boolExprToFormula e2)
                                          in if op == REq then f else FNot f
                     | otherwise      = FPred $ pAtom op (exprToTerm e1) (exprToTerm e2)

-- Convert boolean expression without pointers to a formula
boolExprToFormula :: Expr -> Formula
boolExprToFormula e@(EVar n)                         = FPred $ pAtom (exprToTerm e) TTrue
boolExprToFormula   (EConst (BoolVal True))          = FTrue
boolExprToFormula   (EConst (BoolVal False))         = FFalse
boolExprToFormula e@(EField s f)                     = FPred $ pAtom (exprToTerm e) TTrue
boolExprToFormula e@(EIndex a i)                     = FPred $ pAtom (exprToTerm e) TTrue
boolExprToFormula   (EUnOp Not e)                    = FNot $ boolExprToFormula e
boolExprToFormula   (EBinOp op e1 e2) | isRelBOp op  = combineExpr (bopToRelOp op) e1 e2
boolExprToFormula   (EBinOp op e1 e2) | isBoolBOp op = FBinOp (bopToBoolOp op) (boolExprToFormula e1) (boolExprToFormula e2)

-- Convert scalar expression without pointers and boolean operators to a term
exprToTerm :: Expr -> Term
exprToTerm (EVar n)             = TVar   n
exprToTerm (EConst (IntVal i))  = TInt   i
exprToTerm (EConst (EnumVal e)) = TEnum  e
exprToTerm (EField s f)         = TField (exprToTerm s) f
exprToTerm (EIndex a i)         = TIndex (exprToTerm a) (exprToTerm i)
exprToTerm (EUnOp AddrOf e)     = TAddr  (exprToTerm e)
exprToTerm (EUnOp op e)         = TUnOp  (uopToArithOp op) (exprToTerm e)
exprToTerm (EBinOp op e1 e2)    = TBinOp (bopToArithOp op) (exprToTerm e1) (exprToTerm e2)
exprToTerm (ESlice e s)         = TSlice (exprToTerm e) s

-- Convert boolean expression to a formula
exprToFormula :: (?pdb::PredicateDB) => Expr -> Formula
exprToFormula e@(EVar   _)                       = combine REq (exprExpandPtr e) ctrue
exprToFormula e@(EField _ _)                     = combine REq (exprExpandPtr e) ctrue
exprToFormula e@(EIndex _ _)                     = combine REq (exprExpandPtr e) ctrue
exprToFormula   (EConst (BoolVal True))          = FTrue
exprToFormula   (EConst (BoolVal False))         = FFalse
exprToFormula   (EUnOp  Not e)                   = FNot $ exprToFormula e
exprToFormula   (EBinOp op e1 e2) | isRelBOp op  = combine (bopToRelOp op) (exprExpandPtr e1) (exprExpandPtr e2)
exprToFormula   (EBinOp op e1 e2) | isBoolBOp op = FBinOp (bopToBoolOp op) (exprToFormula e1) (exprToFormula e2)


-- Weakest precondition of a formula wrt a statement
updateFormStat :: Formula -> Statement -> Formula
updateFormStat f (SAssume e)     = FBinOp Conj f (exprToFormula e)
updateFormStat f (SAssign e1 e2) = foldl' (\f (e1,e2) -> updateFormAsn e1 e2 f) f $ zip sc1 sc2
    where sc1 = exprScalars e1 
          sc2 = exprScalars e2

-- Formula update by assignment statement
updateFormAsn :: Expr -> Expr -> Formula -> Formula
updateFormAsn lhs rhs f = 
    foldl' (\f p -> FReplace f p (updatePredAsn lhs rhs p)) f $ formPreds f

-- Predicate update by assignment statement
updatePredAsn :: Expr -> Expr -> Predicate -> Formula
updatePredAsn lhs rhs p = pSubstScalCas p sc'
    sc' = map (updateScalAsn lhs rhs) $ pScalars p
 
-- Takes lhs and rhs of assignment statement and a term
-- Computes possible overlaps of the lhs with the term and
-- corresponding next-state values of the term expressed as concatenation 
-- of slices of the rhs and the original term.
updateScalAsn :: Expr -> Expr -> Term -> Cascade Expr
updateScalAsn e                rhs (TSlice t s) = casSlice (updateScalAsn e rhs t) s
updateScalAsn (ESlice e (l,h)) rhs t            = 
    casMap (\b -> if b
                     then tConcat $
                          (if l == 0 then [] else [termToExpr $ TSlice t (0,l-1)] ++
                          [ESlice rhs (l,h)] ++
                          if h == w - 1 then [] else [termToExpr $ TSlice t (h+1, w - 1)])
                     else termToExpr t) 
           $ lhsTermEq e t
    where w = exprWidth e
updateScalAsn lhs              rhs t            = 
    casMap (\b -> if b then rhs else termToExpr t) $ lhsTermEq lhs t


-- Takes lhs expression and a term and computes the condition 
-- when the expression is a synonym of the term.
lhsTermEq :: Expr -> Term -> Cascade Bool
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
pSubstScalCas :: Predicate -> [Cascade Expr] -> Formula
pSubstScalCas (PAtom op t1 t2) cas = (\e1 e2 -> exprToFormulaModified (consider special case of *x=y) $ EBinOp (relOpToBOp op) e1 e2) <$> t1' <*> t2'
    where (t1', cas') = tSubstCas t1 cas
          (t2', _   ) = tSubstCas t2 cas'

tSubstCas :: Term -> [Cascade Expr] -> (Cascade Expr, [Cascade Expr])
tSubstCas   (TVar   _)           cas = (head cas              , tail cas)
tSubstCas t@(TInt   _)           cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TEnum  _)           cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TTrue  _)           cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TAddr (TVar _))     cas = (CasLeaf $ termToExpr t, cas)
tSubstCas   (TAddr (TField s f)) cas = mapFst (casMap (\(EUnOp AddrOf e) -> CasLeaf $ EUnOp AddrOf (EField e f))) 
                                              $ tSubstCas (TAddr s)
tSubstCas   (TAddr (TIndex a i)) cas = let (a', cas1) = mapFst (casMap (\(EUnOp AddrOf e) -> EUnOp AddrOf (EField e f))) 
                                                               $ tSubstCas (TAddr a)
                                           (i', cas2) = tSubstCas i cas'
                                       in ((\a i -> CasLeaf $ EIndex a i) <$> a' <*> i', cas2)
tSubstCas   (TField _ _)         cas = (head cas              , tail cas)
tSubstCas   (TIndex _ _)         cas = (head cas              , tail cas)
tSubstCas   (TUnOp  op t)        cas = mapFst (casMap (\e -> EUnOp (arithOpToUOp op) t)) $ tSubstCas t
tSubstCas   (TBinOp op t1 t2)    cas = let (t1', cas1) = tSubstCas t1 cas
                                           (t2', cas2) = tSubstCas t2 cas1
                                       in ((\e1 e2 -> EBinOp (arithOpToBOp op) e1 e2) <$> t1' <*> t2', cas2)
tSubstCas   (TSlice t s)         cas = mapFst (casMap (\e -> eSlice e s)) $ tSubstCas t
