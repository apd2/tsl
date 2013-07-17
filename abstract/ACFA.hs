{-# LANGUAGE ImplicitParams, TupleSections #-}

module ACFA(tranCFAToACFA,
            bexprToFormula,
            bexprToFormulaPlus,
            pruneCFAVar) where

import qualified Data.Graph.Inductive as G
import Data.List
import Data.Maybe
import Data.Functor
import qualified Data.Map as M
import Control.Applicative

import Util
import TSLUtil
import Cascade
import Predicate
import BFormula
import ISpec
import IExpr
import IType
import CFA
import Ops
import ACFACompile

-- Compute ACFA for a list of abstract variables for a location inside
-- transition CFA. 
tranCFAToACFA :: (?spec::Spec, ?pred::[Predicate]) => [AbsVar] -> Loc -> CFA -> ACFA
tranCFAToACFA vs loc cfa = 
    let ?initloc = loc 
        ?cfa = cfaPruneUnreachable cfa [loc] in 
    let -- prefill ACFA for final states
        acfa0 = foldl' (\g l -> addUseDefVar g l $ map (,l) vs) G.empty
                $ filter ((==0) . G.outdeg ?cfa)
                $ G.nodes ?cfa
    in mkACFA acfa0 []



mkACFA :: (?spec::Spec, ?initloc::Loc, ?pred::[Predicate], ?cfa::CFA) => ACFA -> [Loc] -> ACFA
mkACFA acfa added = 
    let -- select a location not from the cache with all successors in the cache,
        loc = head
              $ filter (all (\n -> elem n added) . G.suc ?cfa)
              $ filter (\n -> notElem n added)
              $ G.nodes ?cfa
        -- compute variable updates along all outgoing transitions
        updates = map (\(loc', tran) -> (loc', tranPrecondition tran, map (varUpdateTran tran) $ fst $ fromJust $ G.lab acfa loc')) $ G.lsuc ?cfa loc
        -- extract the list of abstract variables from transitions
        vs = nub $ concatMap (\(_,pre,upd) -> formAbsVars pre ++ concatMap acasAbsVars upd) updates
        acfa'  = addUseDefVar acfa loc $ map (\v -> (v, varRecomputedLoc loc v)) vs
        acfa'' = foldIdx (\gr (l, pre, upds) i -> G.insEdge (loc, l, (i,pre,upds)) gr) acfa' updates
    in if loc == ?initloc
          then acfa''
          else mkACFA acfa'' (loc:added)

pruneCFAVar :: (?spec::Spec, ?pred::[Predicate]) => [AbsVar] -> CFA -> CFA
pruneCFAVar avs cfa = foldl' (\g l -> if' (elem l keep) g (G.delNode l g)) cfa (G.nodes cfa)
    where
    -- Find all transitions that update variable values
    trs = filter (\(_,_,tr) -> any (\av -> isVarRecomputedByTran av tr) avs) 
          $ G.labEdges cfa
    -- Find all predecessors and successors of these transitions
    reach = concatMap (\(_,to,_) -> G.dfs  [to] cfa) trs
    preds  = concatMap (\(fr,_,_) -> G.rdfs [fr] cfa) trs
    keep  = nub $ reach ++ preds


varRecomputedLoc :: (?spec::Spec, ?pred::[Predicate], ?cfa::CFA) => Loc -> AbsVar -> Loc
varRecomputedLoc l v | null (G.pre ?cfa l)                                 = l
                     | any (isVarRecomputedByTran v . snd) (G.lpre ?cfa l) = l
                     | all (== pre0) pres                                  = pre0
                     | otherwise                                           = l
    where (pre0:pres) = map (\l' -> varRecomputedLoc l' v) $ G.pre ?cfa l

isVarRecomputedByTran :: (?spec::Spec, ?pred::[Predicate]) => AbsVar -> TranLabel -> Bool
isVarRecomputedByTran v@(AVarTerm t) tr = case varUpdateTran tr v of
                                               Left  (CasLeaf t')         -> t' /= t
                                               Right (CasLeaf f)          -> f  /= (ptrFreeBExprToFormula $ termToExpr t)
                                               _                          -> True
isVarRecomputedByTran v@(AVarPred p) tr = case varUpdateTran tr v of
                                               Right (CasLeaf (FPred p')) -> p' /= p
                                               _                          -> True

-- Takes a location and a list of variables used in this location and updates
-- the corresponding use and defined lists.
addUseDefVar :: ACFA -> Loc -> [(AbsVar, Loc)] -> ACFA
addUseDefVar acfa useloc defs = 
    foldl' (\acfa' (v, defloc) -> let acfa1 = graphUpdNode useloc (\(def, use) -> (def, M.insert v defloc use)) acfa'
                                  in case G.lab acfa1 defloc of
                                          Nothing -> G.insNode (defloc, ([v], M.empty)) acfa1
                                          Just _  -> graphUpdNode defloc (\(def, use) -> (nub $ v:def, use)) acfa1)
           acfa0 defs
    where
    acfa0 = case G.lab acfa useloc of
                 Nothing -> G.insNode (useloc, ([], M.empty)) acfa
                 Just _  -> acfa

-- Precondition of a transition
tranPrecondition :: (?spec::Spec, ?pred::[Predicate]) => TranLabel -> Formula
tranPrecondition (TranStat (SAssume e))   = ptrFreeBExprToFormula e
tranPrecondition _                        = FTrue

-- Compute variable updates for an individual CFA edge
varUpdateTran :: (?spec::Spec, ?pred::[Predicate]) => TranLabel -> AbsVar -> ACascade
varUpdateTran (TranStat (SAssign e1 e2)) v            = varUpdateAsnStat1 e1 e2 v
varUpdateTran _                          (AVarPred p) = Right $ CasLeaf $ bexprToFormula $ predToExpr p
varUpdateTran _                          (AVarTerm t) = Left  $ CasLeaf t

-- Individual variable update for an assignment statement
varUpdateAsnStat1 :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> AbsVar -> ACascade
varUpdateAsnStat1 lhs rhs (AVarPred p) = Right $ CasLeaf $ updatePredAsn lhs rhs p
varUpdateAsnStat1 lhs rhs (AVarTerm t) = --Left  $ fmap exprToTerm $ casMap exprExpandPtr $ updateScalAsn lhs rhs t
    let upd = casMap exprExpandPtr $ updateScalAsn lhs rhs t in
    case typ t of
         Bool -> Right $ CasLeaf $ fcasToFormula $ fmap ptrFreeBExprToFormula upd
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
updateScalAsn :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Term -> ECascade
updateScalAsn lhs rhs t = {-trace ("updateScalAsn(" ++ show t ++ ") " ++ show lhs ++ ":=" ++ show rhs ++ " = " ++ render (nest' $ pp res))-} res
    where res = updateScalAsn' lhs rhs t

updateScalAsn' :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Term -> ECascade
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
lhsTermEq :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Term -> BCascade
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
pSubstScalCas :: (?spec::Spec, ?pred::[Predicate]) => Predicate -> [ECascade] -> Formula
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


-- Convert boolean expression (possibly with pointers) to a formula without
-- introducing new pointer predicates.
bexprToFormula :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Formula
bexprToFormula e = fcasToFormula $ fmap ptrFreeBExprToFormula $ exprExpandPtr e

-- Convert boolean expression (possibly with pointers) to a formula, 
-- introducing new pointer predicates if needed.
bexprToFormulaPlus :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Formula
bexprToFormulaPlus e@(EBinOp op e1 e2) | op == Eq || op == Neq = 
    let f1 = case e1 of
                  EUnOp Deref e1' -> fcasToFormula $ fcasPrune $ (addrPred op) <$> (exprExpandPtr e1') <*> (exprExpandPtr e2)
                  _               -> FFalse
        f2 = case e2 of
                  EUnOp Deref e2' -> fcasToFormula $ fcasPrune $ (addrPred op) <$> (exprExpandPtr e2') <*> (exprExpandPtr e1)
                  _               -> FFalse
    in fdisj $ (bexprToFormula e):[f1,f2]

bexprToFormulaPlus e = bexprToFormula e

-- Check if predicate (x == addrof y) exists in the DB.  If yes,
-- return false, else return (x == addrof y) or !(x == addrof y),
-- depending on op.
addrPred :: (?spec::Spec, ?pred::[Predicate]) => BOp -> Expr -> Expr -> Formula
addrPred op x y =
    let tx = exprToTerm x
        ty = exprToTerm y
        fp = fAtom REq tx (TAddr ty)
    in if (not $ isMemTerm ty) || (any ((==ty) . snd) $ ptrPreds x)
          then FFalse
          else if op == Eq
                  then fp 
                  else fnot fp


-- Expand each pointer dereference operation in the expression
-- using predicates in the DB.
exprExpandPtr :: (?pred::[Predicate]) => Expr -> ECascade
exprExpandPtr e@(EVar _)          = CasLeaf e
exprExpandPtr e@(EConst _)        = CasLeaf e
exprExpandPtr   (EField e f)      = fmap (\e' -> EField e' f) $ exprExpandPtr e
exprExpandPtr   (EIndex a i)      = EIndex <$> exprExpandPtr a <*> exprExpandPtr i
exprExpandPtr   (EUnOp Deref e)   = casMap (CasTree . (map (\(p, t) -> (FPred p, CasLeaf $ termToExpr t))) . ptrPreds)
                                           $ exprExpandPtr e
exprExpandPtr   (EUnOp op e)      = fmap (EUnOp op) $ exprExpandPtr e
exprExpandPtr   (EBinOp op e1 e2) = (EBinOp op) <$> exprExpandPtr e1 <*> exprExpandPtr e2
exprExpandPtr   (ESlice e s)      = fmap (\e' -> ESlice e' s) $ exprExpandPtr e

-- Find predicates of the form (e == AddrOf e')
ptrPreds :: (?pred::[Predicate]) => Expr -> [(Predicate, Term)]
ptrPreds e = 
    mapMaybe (\p@(PAtom _ t1 t2) -> if t1 == t
                                       then case t2 of
                                                 TAddr t' -> Just (p,t')
                                                 _        -> Nothing
                                       else if t2 == t
                                               then case t1 of
                                                         TAddr t' -> Just (p,t')
                                                         _        -> Nothing
                                               else Nothing) 
             ?pred
    where t = exprToTerm e
