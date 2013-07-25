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
        acfa0 = foldl' (\g l -> addUseDefVar g l $ map (\v -> (v, varRecomputedLoc loc v)) vs) G.empty
                $ filter ((==0) . G.outdeg ?cfa)
                $ G.nodes ?cfa
    in simplifyACFA $ mkACFA acfa0 []

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
        vs = nub $ concatMap (\(_,mpre,upd) -> maybe [] fAbsVars mpre ++ concatMap acasAbsVars upd) updates
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
    preds = concatMap (\(fr,_,_) -> G.rdfs [fr] cfa) trs
    keep  = nub $ reach ++ preds


varRecomputedLoc :: (?spec::Spec, ?pred::[Predicate], ?cfa::CFA) => Loc -> AbsVar -> Loc
varRecomputedLoc l v | null (G.pre ?cfa l)                                 = l
                     | any (isVarRecomputedByTran v . snd) (G.lpre ?cfa l) = l
                     | all (== pre0) pres                                  = pre0
                     | otherwise                                           = l
    where (pre0:pres) = map (\l' -> varRecomputedLoc l' v) $ G.pre ?cfa l

isVarRecomputedByTran :: (?spec::Spec, ?pred::[Predicate]) => AbsVar -> TranLabel -> Bool
isVarRecomputedByTran v tr = case varUpdateTran tr v of
                                  CasLeaf e -> e /= avarToExpr v
                                  _         -> True


simplifyACFA :: ACFA -> ACFA
simplifyACFA acfa = if' (b1 || b2 || b3) (simplifyACFA acfa3) acfa
    where (acfa1, b1) = simplifyACFA1 acfa
          (acfa2, b2) = simplifyACFA2 acfa1
          (acfa3, b3) = simplifyACFA3 acfa2
          -- TODO: after simplifyACFA3 some variable updates
          -- may be redundant.

-- Find and delete a location that
-- * has a single outgoing transition that does not contain any variable
--   updates or preconditions
-- * does not contain any variable updates
simplifyACFA1 :: ACFA -> (ACFA, Bool)
simplifyACFA1 acfa = maybe (acfa, False) ((, True) . rm acfa) mcand
    where mcand = find ((\(_, mpre, upds) -> isNothing mpre && null upds) . snd . head . G.lsuc acfa)
                  $ filter ((==1) . length . G.lsuc acfa)
                  $ filter ((>0)  . length . G.pre acfa)  -- not initial location
                  $ filter (null  . fst . fromJust . G.lab acfa)
                  $ G.nodes acfa
          rm :: ACFA -> Loc -> ACFA
          rm g c = foldl' (\g' (c'', l) -> G.insEdge (c'',c', l) g') (G.delNode c g) (G.lpre g c)
              where c' = head $ G.suc g c

-- Find a location that
-- * has a single outgoing edge to a location that only has one predecessor
-- * this edge does not contain preconditions or variable updates
-- and delete this successor location
simplifyACFA2 :: ACFA -> (ACFA, Bool)
simplifyACFA2 acfa = maybe (acfa, False) ((, True) . rm acfa) mcand
    where mcand = find ((\(_, mpre, upds) -> isNothing mpre && null upds) . snd . head . G.lsuc acfa)
                  $ filter ((==1) . length . G.pre acfa . head . G.suc acfa)
                  $ filter ((==1) . length . G.lsuc acfa)
                  $ filter ((>0)  . length . G.pre acfa)
                  $ G.nodes acfa
          rm :: ACFA -> Loc -> ACFA
          rm g c = foldl' (\g' (c'', l) -> G.insEdge (c,c'', l) g') (G.delNode c' g0) (G.lsuc g0 c')
              where (def,_) = fromJust $ G.lab g c
                    c' = head $ G.suc g c
                    (_,use) = fromJust $ G.lab g c' 
                    g0 = graphUpdNode c (\_ -> (def,use)) g


-- eliminate conditional nodes (i.e., nodes that have >1 outgoing edges labelled 
-- with preconditions, but no var updates) in case they only have a single successor.
-- The assumption here is that all branches are of the form if-then-else, i.e., 
-- disjunction of branch conditions is true.
simplifyACFA3 :: ACFA -> (ACFA, Bool)
simplifyACFA3 acfa = maybe (acfa, False) ((,True) . rm acfa) mcand
    where mcand = find     (all ((\(_,mpre,upd) -> null upd && isJust mpre) . snd) . G.lsuc acfa)
                  $ filter ((==1) . length . nub . G.suc acfa)
                  $ filter ((>1)  . length . G.lsuc acfa)
                  $ G.nodes acfa     
          rm :: ACFA -> Loc -> ACFA
          rm g c = graphUpdNode c (\(def, _) -> (def,M.empty))
                   $ G.insEdge (c, c', (0, Nothing, [])) 
                   $ G.delEdge (c,c') g
                   where c' = head $ G.suc g c

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
tranPrecondition :: (?spec::Spec, ?pred::[Predicate]) => TranLabel -> Maybe Formula
tranPrecondition (TranStat (SAssume e))   = Just $ ptrFreeBExprToFormula e
tranPrecondition _                        = Nothing

-- Compute variable updates for an individual CFA edge
varUpdateTran :: (?spec::Spec, ?pred::[Predicate]) => TranLabel -> AbsVar -> ECascade
varUpdateTran (TranStat (SAssign e1 e2)) v = fmap (\e -> if' (isConstExpr e) (EConst $ evalConstExpr e) e) $ updateExprAsn e1 e2 (avarToExpr v)
varUpdateTran _                          v = CasLeaf $ avarToExpr v

updateExprAsn :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> ECascade
updateExprAsn lhs rhs e = casMap (updateExprAsn' lhs rhs) $ updateExprIndices lhs rhs e

updateExprAsn' :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> ECascade
updateExprAsn' lhs rhs e@(EVar _)          = updateScalAsn lhs rhs e
updateExprAsn' _   _   e@(EConst _)        = CasLeaf e
updateExprAsn' lhs rhs e@(EField _ _)      = updateScalAsn lhs rhs e
updateExprAsn' lhs rhs e@(EIndex _ _)      = updateScalAsn lhs rhs e
updateExprAsn' _   _   e@(EUnOp AddrOf _)  = CasLeaf e
updateExprAsn' lhs rhs   (EUnOp op e)      = fmap (EUnOp op) $ updateExprAsn' lhs rhs e
updateExprAsn' lhs rhs   (EBinOp op e1 e2) = (EBinOp op) <$> updateExprAsn' lhs rhs e1 <*> updateExprAsn' lhs rhs e2
updateExprAsn' lhs rhs   (ESlice e s)      = fmap (\e' -> exprSlice e' s) $ updateExprAsn' lhs rhs e

-- apply updateExprAsn to all array indices in the expression
updateExprIndices :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> ECascade
updateExprIndices _   _   e@(EVar _)          = CasLeaf e
updateExprIndices _   _   e@(EConst _)        = CasLeaf e
updateExprIndices lhs rhs   (EField s f)      = fmap (\s' -> EField s' f) $ updateExprIndices lhs rhs s
updateExprIndices lhs rhs   (EIndex a i)      = (\a' i' -> EIndex a' i') <$> updateExprIndices lhs rhs a <*> updateExprAsn lhs rhs i
updateExprIndices lhs rhs   (EUnOp op e)      = fmap (EUnOp op) $ updateExprIndices lhs rhs e
updateExprIndices lhs rhs   (EBinOp op e1 e2) = (EBinOp op) <$> updateExprIndices lhs rhs e1 <*> updateExprIndices lhs rhs e2
updateExprIndices lhs rhs   (ESlice e s)      = fmap (\e' -> ESlice e' s) $ updateExprIndices lhs rhs e

-- Takes lhs and rhs of assignment statement and a term
-- Computes possible overlaps of the lhs with the term and
-- corresponding next-state values of the term expressed as concatenation 
-- of slices of the rhs and the original term.
updateScalAsn :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> ECascade
updateScalAsn lhs rhs x = casMap exprExpandPtr $ updateScalAsn' lhs rhs x

updateScalAsn' :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> ECascade
updateScalAsn' lhs              rhs (ESlice x s) = fmap (\e' -> exprSlice e' s) (updateScalAsn' lhs rhs x)
updateScalAsn' (ESlice e (l,h)) rhs x            = 
    fmap (\b -> if b
                   then econcat $
                        (if l == 0 then [] else [exprSlice x (0,l-1)]) ++
                        [rhs] ++
                        (if h == w - 1 then [] else [exprSlice x (h+1, w - 1)])
                   else x) 
         $ lhsExprEq e x
    where w = typeWidth e
updateScalAsn' lhs              rhs x            = 
    fmap (\b -> if b then rhs else x) $ lhsExprEq lhs x


-- Takes lhs expression and a term and computes the condition 
-- when the expression is a synonym of the term.
lhsExprEq :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> BCascade
lhsExprEq (EVar n1)      (EVar n2)        | n1 == n2 = CasLeaf True
lhsExprEq (EField e1 f1) (EField e2 f2)   | f1 == f2 = lhsExprEq e1 e2
lhsExprEq (EIndex a1 i1) (EIndex a2 i2)              = 
    casMap (\b -> if b 
                     then case bexprToFormula $ i1 === i2 of
                               FTrue  -> CasLeaf True
                               FFalse -> CasLeaf False
                               f      -> CasTree [(f, CasLeaf True), (fnot f, CasLeaf False)]
                     else CasLeaf False)
           $ lhsExprEq a1 a2
lhsExprEq (EUnOp Deref e1) e2             | t1 == t2 && isMemExpr e2 = 
    case bexprToFormula $ e1 === EUnOp AddrOf e2 of
         FTrue  -> CasLeaf True
         FFalse -> CasLeaf False
         f      -> CasTree [(f, CasLeaf True), (fnot f, CasLeaf False)]
    where Ptr t1 = typ e1
          t2     = typ e2
lhsExprEq _              _                           = CasLeaf False


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
    let fp = fRel REq x (EUnOp AddrOf y)
    in if (not $ isMemExpr y) || (any ((==y) . termToExpr . snd) $ ptrPreds x)
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
exprExpandPtr   (EUnOp Deref e)   = casMap (CasTree . (map (\(p, t) -> (FBoolAVar $ AVarPred p, CasLeaf $ termToExpr t))) . ptrPreds)
                                           $ exprExpandPtr e
exprExpandPtr   (EUnOp op e)      = fmap (EUnOp op) $ exprExpandPtr e
exprExpandPtr   (EBinOp op e1 e2) = (EBinOp op) <$> exprExpandPtr e1 <*> exprExpandPtr e2
exprExpandPtr   (ESlice e s)      = fmap (\e' -> ESlice e' s) $ exprExpandPtr e

-- Find predicates of the form (e == AddrOf e')
ptrPreds :: (?pred::[Predicate]) => Expr -> [(Predicate, Term)]
ptrPreds e = 
    mapMaybe (\p@(PAtom _ pt1 pt2) -> case (pt1, pt2) of
                                           (PTPtr t1, PTPtr t2) -> if' (termToExpr t1 == e) 
                                                                       (case t2 of
                                                                             TAddr t' -> Just (p,t')
                                                                             _        -> Nothing)
                                                                       (if' (termToExpr t2 == e)
                                                                            (case t1 of
                                                                                  TAddr t' -> Just (p,t')
                                                                                  _        -> Nothing)
                                                                            Nothing))
             ?pred
