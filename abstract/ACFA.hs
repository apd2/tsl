{-# LANGUAGE ImplicitParams, TupleSections #-}

module ACFA(tranCFAToACFA) where

import qualified Data.Graph.Inductive as G
import Data.List

import Cascade
import Predicate
import BFormula
import ISpec
import CFA
import ACFACompile

-- Compute ACFA for a list of abstract variables for a location inside
-- transition CFA. 
tranCFAToACFA :: (?spec::Spec, ?pred::[Predicate]) => [AbsVar] -> Loc -> CFA -> ACFA
tranCFAToACFA vs loc cfa = 
    let ?initloc = loc 
        ?cfa = cfaPruneUnreachable cfa loc in 
    let -- prefill cache for final states
        acfa0 = foldl' (\g l -> G.insNode (l,vs) g) G.empty
                $ filter ((==0) . G.outdeg cfa)
                $ G.nodes cfa
    in mkACFA acfa0

mkACFA :: (?initloc::Loc, ?pred::[Predicate], ?cfa::CFA) => ACFA -> ACFA
mkACFA acfa = 
    let -- select a location not from the cache with all successors in the cache,
        loc = head
              $ filter (all (\n -> elem n $ G.nodes acfa) . G.suc ?cfa)
              $ filter (\n -> notElem n $ G.nodes acfa)
              $ G.nodes ?cfa
        -- compute variable updates along all outgoing transitions
        updates = map (\(loc', tran) -> map ((loc', ) . varUpdateTran tran) $ G.lab acfa loc') $ G.lsuc ?cfa loc
        -- extract the list of abstract variables from transitions
        vs = nub 
             $ concatMap (acasAbsVars . snd) 
             $ concat updates
        acfa' = foldIdx (\gr (l, upds) i -> G.insEdge (loc, l, (i,upds)) gr)
                (G.insNode (loc, vs) acfa) updates
    in if loc == ?initloc
          then acfa'
          else mkACFA acfa'

-- Compute variable updates for an individual CFA edge
varUpdateTran :: (?spec::Spec, ?pred::[Predicate]) => TranLabel -> AbsVar -> ACascade
varUpdateTran (TranStat (SAssume e))     (AVarPred p) = Right $ CasTree [bexprToFormulaPlus e, CasLeaf $ bexprToFormula $ predToExpr p] 
varUpdateTran (TranStat (SAssume e))     (AVarTerm t) = Left  $ CasTree [bexprToFormulaPlus e, CasLeaf t] 
varUpdateTran (TranStat (SAssign e1 e2)) v            = varUpdateAsnStat1 e1 e2 v
varUpdateTran _                          (AVarPred p) = Right $ CasLeaf $ bexprToFormula $ predToExpr v
varUpdateTran _                          (AVarTerm t) = Left  $ CasLeaf t

-- Individual variable update for an assignment statement
varUpdateAsnStat1 :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> AbsVar -> ACascade
varUpdateAsnStat1 lhs rhs (AVarPred p) = Right $ CasLeaf $ updatePredAsn lhs rhs p
varUpdateAsnStat1 lhs rhs (AVarTerm t) = 
    let upd = casMap exprExpandPtr $ updateScalAsn lhs rhs t in
    case typ t of
         Bool -> Right $ CasLeaf $ fcasToFormula $ fmap bexprToFormula' upd
         _    -> Left  $ fmap exprToTerm upd
 
-- Predicate update by assignment statement
updatePredAsn :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Predicate -> Formula
updatePredAsn lhs rhs p = {-trace ("updatePredAsn (" ++ show lhs ++ ":=" ++ show rhs ++ ", " ++ show p ++ ") = " ++ show res)-} res
    where sc' = map (updateScalAsn lhs rhs) $ pScalars p
          res = pSubstScalCas p sc'
 
-- Takes lhs and rhs of assignment statement and a term
-- Computes possible overlaps of the lhs with the term and
-- corresponding next-state values of the term expressed as concatenation 
-- of slices of the rhs and the original term.
updateScalAsn :: (?spec::Spec, ?pred::[Predicate], ?m::C.STDdManager s u) => Expr -> Expr -> Term -> ECascade
updateScalAsn lhs rhs t = {-trace ("updateScalAsn(" ++ show t ++ ") " ++ show lhs ++ ":=" ++ show rhs ++ " = " ++ render (nest' $ pp res))-} res
    where res = updateScalAsn' lhs rhs t

updateScalAsn' :: (?spec::Spec, ?pred::[Predicate], ?m::C.STDdManager s u) => Expr -> Expr -> Term -> ECascade
updateScalAsn' e                rhs (TSlice t s) = fmap (\e' -> exprSlice e' s) (updateScalAsn' e rhs t)
updateScalAsn' (ESlice e (l,h)) rhs t            = 
    fmap (\b -> if b
                   then econcat $
                        (if l == 0 then [] else [termToExpr $ TSlice t (0,l-1)]) ++
                        [rhs] ++
                        (if h == w - 1 then [] else [termToExpr $ TSlice t (h+1, w - 1)])
                   else termToExpr t) 
         $ lhsTermEq e t
    where w = typeWidth e
updateScalAsn' lhs              rhs t            = 
    fmap (\b -> if b then rhs else termToExpr t) $ lhsTermEq lhs t


-- Takes lhs expression and a term and computes the condition 
-- when the expression is a synonym of the term.
lhsTermEq :: (?spec::Spec, ?pred::[Predicate], ?m::C.STDdManager s u) => Expr -> Term -> BCascade
lhsTermEq (EVar n1)       (TVar n2)        | n1 == n2 = CasLeaf True
lhsTermEq (EField e f1)   (TField t f2)    | f1 == f2 = lhsTermEq e t
lhsTermEq (EIndex ae ie)  (TIndex at it)              = 
    casMap (\b -> if b 
                     then case bexprToFormula $ (termToExpr it) === ie of
                               FTrue  -> CasLeaf True
                               FFalse -> CasLeaf False
                               f      -> CasTree [(f, CasLeaf True), (fnot f, CasLeaf False)]
                     else CasLeaf False)
           $ lhsTermEq ae at
lhsTermEq (EUnOp Deref e) t                | etyp == ttyp && isMemTerm t = 
    case bexprToFormula $ e === EUnOp AddrOf (termToExpr t) of
         FTrue  -> CasLeaf True
         FFalse -> CasLeaf False
         f      -> CasTree [(f, CasLeaf True), (fnot f, CasLeaf False)]
    where Ptr etyp = typ e
          ttyp     = typ t
lhsTermEq _              _                            = CasLeaf False


-- Extract scalar variables terms from predicate
pScalars :: Predicate -> [Term]
pScalars (PAtom _ t1 t2) = tScalars t1 ++ tScalars t2

tScalars :: Term -> [Term]
tScalars t@(TVar   _)           = [t]
tScalars   (TSInt  _ _)         = []
tScalars   (TUInt  _ _)         = []
tScalars   (TEnum  _)           = []
tScalars   TTrue                = []
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
pSubstScalCas :: (?spec::Spec, ?pred::[Predicate], ?m::C.STDdManager s u) => Predicate -> [ECascade] -> Formula
pSubstScalCas (PAtom op t1 t2) cas = fcasToFormula $ (\e1 e2 -> bexprToFormulaPlus $ EBinOp (relOpToBOp op) e1 e2) <$> t1' <*> t2'
    where (t1', cas') = tSubstCas t1 cas
          (t2', _   ) = tSubstCas t2 cas'

tSubstCas :: (?spec::Spec, ?pred::[Predicate]) => Term -> [ECascade] -> (ECascade, [ECascade])
tSubstCas   (TVar   _)           cas = (head cas              , tail cas)
tSubstCas t@(TSInt  _ _)         cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TUInt  _ _)         cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TEnum  _)           cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@TTrue                cas = (CasLeaf $ termToExpr t, cas)
tSubstCas t@(TAddr (TVar _))     cas = (CasLeaf $ termToExpr t, cas)
tSubstCas   (TAddr (TField s f)) cas = mapFst (fmap (\(EUnOp AddrOf e) -> EUnOp AddrOf (EField e f))) 
                                              $ tSubstCas (TAddr s) cas
tSubstCas   (TAddr (TIndex a i)) cas = let (a', cas1) = mapFst (fmap (\(EUnOp AddrOf e) -> e ))
                                                               $ tSubstCas (TAddr a) cas
                                           (i', cas2) = tSubstCas i cas1
                                       in ((\ar ind -> EUnOp AddrOf $ EIndex ar ind) <$> a' <*> i', cas2)
tSubstCas   (TField _ _)         cas = (head cas              , tail cas)
tSubstCas   (TIndex _ _)         cas = (head cas              , tail cas)
tSubstCas   (TUnOp  op t)        cas = mapFst (fmap (\e -> EUnOp (arithOpToUOp op) e)) $ tSubstCas t cas
tSubstCas   (TBinOp op t1 t2)    cas = let (t1', cas1) = tSubstCas t1 cas
                                           (t2', cas2) = tSubstCas t2 cas1
                                       in ((\e1 e2 -> EBinOp (arithOpToBOp op) e1 e2) <$> t1' <*> t2', cas2)
tSubstCas   (TSlice t s)         cas = mapFst (fmap (\e -> exprSlice e s)) $ tSubstCas t cas
