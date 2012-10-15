{-# LANGUAGE ImplicitParams #-}

module TSLAbsGame(tslAbsGame) where

import Control.Monad.State
import Control.Applicative
import Data.Functor
import Data.Maybe

import Common
import AbsGame
import LogicClasses
import ISpec
import IExpr
import IType
import Cascade
import Predicate
import Formula

-----------------------------------------------------------------------
-- Interface
-----------------------------------------------------------------------

tslAbsGame :: (AllOps c v a) => Spec -> AbsGame c v a Predicate
tslAbsGame spec = AbsGame { gameGoals       = tslGameGoals       spec
                          , gameFair        = tslGameFair        spec
                          , gameInit        = tslGameInit        spec
                          , gamePredUpdateC = tslGamePredUpdateC spec
                          , gamePredUpdateU = tslGamePredUpdateU spec
                          , gameBoolUpdateC = tslGameBoolUpdateC spec
                          , gameBoolUpdateU = tslGameBoolUpdateU spec
                          , gameEnumUpdateC = tslGameEnumUpdateC spec
                          , gameEnumUpdateU = tslGameEnumUpdateU spec}


tslGameGoals :: (AllOps c v a) => Spec -> State (PredicateDB c v Predicate) [(String,a)]
tslGameGoals spec = mapM (\g -> do c <- bexprAbstract spec (goalCond g)
                                   return (goalName g, c))
                         $ specGoal spec

tslGameFair :: (AllOps c v a) => Spec -> State (PredicateDB c v Predicate) [a]
tslGameFair spec = mapM (bexprAbstract spec) $ specFair spec

tslGameInit :: (AllOps c v a) => Spec -> State (PredicateDB c v Predicate) a
tslGameInit spec = bexprAbstract spec (specInit spec)

tslGamePredUpdateC :: (AllOps c v a) => Spec -> Predicate -> State (PredicateDB c v Predicate) a
tslGamePredUpdateC = error "Not implemented: tslGamePredUpdateC"

tslGamePredUpdateU :: (AllOps c v a) => Spec -> Predicate -> State (PredicateDB c v Predicate) a
tslGamePredUpdateU = error "Not implemented: tslGamePredUpdateU"

tslGameBoolUpdateC :: (AllOps c v a) => Spec -> String -> State (PredicateDB c v Predicate) a
tslGameBoolUpdateC = error "Not implemented: tslGameBoolUpdateC"

tslGameBoolUpdateU :: (AllOps c v a) => Spec -> String -> State (PredicateDB c v Predicate) a
tslGameBoolUpdateU = error "Not implemented: tslGameBoolUpdateU"

tslGameEnumUpdateC :: (AllOps c v a) => Spec -> String -> State (PredicateDB c v Predicate) a
tslGameEnumUpdateC = error "Not implemented: tslGameEnumUpdateC"

tslGameEnumUpdateU :: (AllOps c v a) => Spec -> String -> State (PredicateDB c v Predicate) a
tslGameEnumUpdateU = error "Not implemented: tslGameEnumUpdateU"

----------------------------------------------------------------------------
-- PDB operations
----------------------------------------------------------------------------

-- Find predicates of the form (e == AddrOf e')
pdbPtrPreds :: (?pdb::PredicateDB c v Predicate) => Expr -> [(Predicate, Term)]
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
             $ map fst $ pdbPred ?pdb
    where t = exprToTerm e

----------------------------------------------------------------------------
-- Compilation
----------------------------------------------------------------------------

-- Extract predicates from formula and compile it
compile :: (AllOps c v a,?spec::Spec) => Formula -> State (PredicateDB c v Predicate) a
compile = error "Not implemented: compile"

----------------------------------------------------------------------------
-- Computing abstraction
----------------------------------------------------------------------------

bexprAbstract :: (AllOps c v a) => Spec -> Expr -> State (PredicateDB c v Predicate) a
bexprAbstract spec e = do
    pdb <- get
    let ?spec = spec
        ?pdb  = pdb
    compile $ bexprToFormula e

-- Convert boolean expression (possibly with pointers) to a formula without
-- introducing new pointer predicates.
bexprToFormula :: (AllOps c v a, ?spec::Spec, ?pdb::PredicateDB c v Predicate) => Expr -> Formula
bexprToFormula e = fcasToFormula $ fmap bexprToFormula' $ exprExpandPtr e

-- Convert boolean expression without pointers to a formula
bexprToFormula' :: (?spec::Spec) => Expr -> Formula
bexprToFormula' e@(EVar n)                         = FPred $ pAtom REq (exprToTerm e) TTrue
bexprToFormula'   (EConst (BoolVal True))          = FTrue
bexprToFormula'   (EConst (BoolVal False))         = FFalse
bexprToFormula' e@(EField s f)                     = FPred $ pAtom REq (exprToTerm e) TTrue
bexprToFormula' e@(EIndex a i)                     = FPred $ pAtom REq (exprToTerm e) TTrue
bexprToFormula'   (EUnOp Not e)                    = FNot $ bexprToFormula' e
bexprToFormula'   (EBinOp op e1 e2) | isRelBOp op  = combineExpr (bopToRelOp op) e1 e2
bexprToFormula'   (EBinOp op e1 e2) | isBoolBOp op = FBinOp (bopToBoolOp op) (bexprToFormula' e1) (bexprToFormula' e2)

combineExpr :: (?spec::Spec) => RelOp -> Expr -> Expr -> Formula
combineExpr op e1 e2 | typ e1 == Bool =
   case e1 of
       EConst (BoolVal True)  -> if op == REq then bexprToFormula' e2 else FNot $ bexprToFormula' e2
       EConst (BoolVal False) -> if op == REq then FNot $ bexprToFormula' e2 else bexprToFormula' e2
       _                      -> 
           case e2 of
                EConst (BoolVal True)  -> if op == REq then bexprToFormula' e1 else FNot $ bexprToFormula' e1
                EConst (BoolVal False) -> if op == REq then FNot $ bexprToFormula' e1 else bexprToFormula' e1
                _                      -> let f = FBinOp Equiv (bexprToFormula' e1) (bexprToFormula' e2)
                                          in if op == REq then f else FNot f
                     | otherwise      = FPred $ pAtom op (exprToTerm e1) (exprToTerm e2)

-- Expand each pointer dereference operation in the expression
-- using predicates in the DB.
exprExpandPtr :: (?pdb::PredicateDB c v Predicate) => Expr -> ECascade
exprExpandPtr e@(EVar _)          = CasLeaf e
exprExpandPtr e@(EConst _)        = CasLeaf e
exprExpandPtr   (EField e f)      = fmap (\e -> EField e f) $ exprExpandPtr e
exprExpandPtr   (EIndex a i)      = EIndex <$> exprExpandPtr a <*> exprExpandPtr i
exprExpandPtr   (EUnOp Deref e)   = casMap (CasTree . (map (\(p, t) -> (FPred p, CasLeaf $ termToExpr t))) . pdbPtrPreds)
                                           $ exprExpandPtr e
exprExpandPtr   (EBinOp op e1 e2) = (EBinOp op) <$> exprExpandPtr e1 <*> exprExpandPtr e2
exprExpandPtr   (ESlice e s)      = fmap (\e -> ESlice e s) $ exprExpandPtr e

----------------------------------------------------------------------------
-- Predicate/variable update functions
----------------------------------------------------------------------------

-- Formula update by a statement
--updateFormStat :: (?spec::Spec) => Formula -> Statement -> Formula
--updateFormStat f (SAssume e)     = FBinOp Conj f (bexprToFormula e)
--updateFormStat f (SAssign e1 e2) = foldl' (\f (e1,e2) -> updateFormAsn e1 e2 f) f $ zip sc1 sc2
--    where sc1 = scalars e1 (typ e1)
--          sc2 = scalars e2 (typ e2)

-- Formula update by assignment statement
--updateFormAsn :: Expr -> Expr -> Formula -> Formula
--updateFormAsn lhs rhs f = 
--    foldl' (\f p -> FReplace f p (updatePredAsn lhs rhs p)) f $ formPreds f



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
                     then case bexprToFormula $ (termToExpr it) === ie of
                               FTrue  -> CasLeaf True
                               FFalse -> CasLeaf False
                               f      -> CasTree [(f, CasLeaf True), (FNot f, CasLeaf False)]
                     else CasLeaf False)
           $ lhsTermEq ae at
lhsTermEq (EUnOp Deref e) t                 | typeMatch etyp ttyp && isMemTerm t = 
    case bexprToFormula $ e === EUnOp AddrOf (termToExpr t) of
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
pSubstScalCas (PAtom op t1 t2) cas = (\e1 e2 -> bexprToFormulaModified $ EBinOp (relOpToBOp op) e1 e2) <$> t1' <*> t2'
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
