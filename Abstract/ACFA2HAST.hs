{-# LANGUAGE ImplicitParams #-}

module Abstract.ACFA2HAST(TAST,
                 ACFA,
                 acfaTraceFile,
                 compileACFA,
                 compileFormula,
                 compileFCas,
                 compileTCas) where

import qualified Data.Graph.Inductive as G
import qualified Data.Map             as M
import Data.List
import Data.Maybe
import Data.Tuple.Select
import GHC.Exts

import Util hiding (trace)
import Ops
import qualified HAST.HAST as H
import Abstract.Cascade
import Abstract.Predicate
import Abstract.BFormula
import Internal.ISpec
import Internal.IType
import Internal.CFA
import Synthesis.Interface
import Abstract.ACFA
import Abstract.CFA2ACFA
import {-# SOURCE #-} Abstract.MkPredicate

type TAST f e c  = H.AST f e c (BAVar AbsVar AbsVar)
type TASTVar f e = H.ASTVar f e (BAVar AbsVar AbsVar)

disj []  = H.F
disj [x] = x
disj xs  = H.Disj xs

conj []  = H.T
conj [x] = x
conj xs  = H.Conj xs


compileACFA :: (?spec::Spec) => [(AbsVar, f)] -> ACFA -> TAST f e c
compileACFA nxtvs acfa = --trace ("ord: " ++ show ord) 
                         -- $ graphTrace (G.emap (\_ -> "") acfa) "ACFA"
                         let ?acfa = acfa in mkAST nxtvs ord
    where
    ord = order []
    order ls = -- pick node with all successors in ls with the highest outbound degree
               case candidates of
                    [] -> ls
                    _  -> order $ (head $ sortWith (\l -> G.indeg acfa l - G.outdeg acfa l) candidates):ls 
               where candidates = filter (\n -> all (\n' -> elem n' ls) $ G.suc acfa n) 
                                $ filter (\n -> notElem n ls)
                                $ G.nodes acfa

-- map of existentially quantified variables
-- * the first component of the tuple stores an existential variable
--   per each location and AbsVar defined in this location.
-- * the second component stores a variable per location and outgoing transition
type EMap f e c = (M.Map (Loc, AbsVar) (TASTVar f e),
                   M.Map (Loc, Int)    (TAST f e c))

showEMap :: EMap f e c -> String
showEMap (vmap, tmap) = "vmap: "   ++ (intercalate ", " $ map (\((l,av),_) -> show (l,av)) $ M.toList vmap) ++ 
                        "\ntmap: " ++ (intercalate ", " $ map (\((l,i),_)  -> show (l,i))  $ M.toList tmap)

mkAST :: (?spec::Spec, ?acfa::ACFA) => [(AbsVar, f)] -> [Loc] -> TAST f e c
mkAST nxtvs ord = mkAST' (vmap1, M.empty) ord
    where -- prefill map for initial and final locations
    vmap0 = foldl' (\m l -> foldl' (\m' (av,v) -> M.insert (l,av) (H.FVar v) m') m nxtvs) M.empty
            $ filter ((==0) . G.outdeg ?acfa)
            $ G.nodes ?acfa
    vmap1 = foldl' (\m l -> foldl' (\m' (av,_,_) -> M.insert (l,av) (H.NVar $ avarBAVar av) m') m (fst $ fromJust $ G.lab ?acfa l)) vmap0
            $ filter ((==0) . G.indeg ?acfa)
            $ G.nodes ?acfa


mkAST' :: (?spec::Spec, ?acfa::ACFA) => EMap f e c -> [Loc] -> TAST f e c
mkAST' _            []      = H.T
mkAST' (vmap, tmap) (l:ord) = 
    H.NExists ("f" ++ show l) 1 
    $ (\xl -> let fl = H.Var $ H.EVar xl in
              H.nExistsMany (map (\(l',_) -> ("f" ++ show l ++ "-" ++ show l', 1)) out)
              $ (\xll -> let fll = map (H.Var . H.EVar) xll in
                         let tmap' = foldl' (\m (v, (_, (i,_,_))) -> M.insert (l,i) v m) tmap $ zip fll out in
                         H.nExistsMany (map (\v -> (show v ++ "-" ++ show l, avarWidth v)) vs)
                         $ (\xs -> let vmap' = foldl' (\m (v, av) -> M.insert (l,av) (H.EVar v) m) vmap $ zip xs vs
                                   in (mkAST' (vmap', tmap') ord)                  `H.And` 
                                      ((fl `H.XNor` if' (null fll) H.T (disj fll)) `H.And`
                                       mkFanin (vmap', tmap') fl))))
    where 
    vs  = filter (\v -> M.notMember (l,v) $ vmap) $ map sel1 $ fst $ fromJust $ G.lab ?acfa l
    out = G.lsuc ?acfa l
    mkFanin emap fl = case G.lpre ?acfa l of
                           []  -> fl
                           pre -> conj $ map (\(l', tr) -> compileTransition emap l' l tr fl) pre


compileTransition :: (?spec::Spec, ?acfa::ACFA) => EMap f e c -> Loc -> Loc -> (Int, Maybe Formula, [MECascade]) -> TAST f e c -> TAST f e c
compileTransition emap from to (idx, mpre, upd) tovar = trvar `H.XNor` (preast `H.And` updast `H.And` tovar)
    where trvar  = (snd emap) M.! (from,idx)
          tovs   = map (\(av,op,_) -> (av,op)) $ fst $ fromJust $ G.lab ?acfa to
          updast = let ?emap = emap
                       ?from = from
                       ?to = to in
                   conj $ map compileTransition1 $ zip upd tovs
          preast = let ?loc = from 
                       ?emap = emap in 
                   maybe H.T compileFormulaLoc mpre


compileTransition1 :: (?spec::Spec, ?acfa::ACFA, ?emap::EMap f e c, ?from::Loc, ?to::Loc) => (MECascade, (AbsVar, LogicOp)) -> TAST f e c
compileTransition1 (cas, (av, op)) = 
    let astvar = (fst ?emap) M.! (?to, av) in
    let ?loc = ?from
    in case av of
            AVarBool _ -> compileFCasLoc (fmap (fmap ptrFreeBExprToFormula) cas) (astvar, op)
            AVarPred _ -> compileFCasLoc (fmap (fmap ptrFreeBExprToFormula) cas) (astvar, op)
            AVarEnum _ -> compileTCasLoc (fmap (fmap scalarExprToTerm)      cas) astvar
            AVarInt  _ -> compileTCasLoc (fmap (fmap scalarExprToTerm)      cas) astvar

compileFCasLoc :: (?spec::Spec, ?acfa::ACFA, ?emap::EMap f e c, ?loc::Loc) => MFCascade -> (TASTVar f e, LogicOp) -> TAST f e c
compileFCasLoc (CasLeaf Nothing)  _  = H.T
compileFCasLoc (CasLeaf (Just f)) (av, Implies) = (H.Var av) `H.Imp` compileFormulaLoc f
compileFCasLoc (CasLeaf (Just f)) (av, Implied) = compileFormulaLoc f `H.Imp` (H.Var av)
compileFCasLoc (CasLeaf (Just f)) (av, Iff)     = (H.Var av) `H.XNor` compileFormulaLoc f
compileFCasLoc (CasTree bs)       (av, op)      = disj $ map (\(f,cas) -> compileFormulaLoc f `H.And` compileFCasLoc cas (av, op)) bs

compileTCasLoc :: (?spec::Spec, ?acfa::ACFA, ?emap::EMap f e c, ?loc::Loc) => MTCascade -> TASTVar f e -> TAST f e c
compileTCasLoc (CasTree bs)                 av                         = disj $ map (\(f,cas) -> compileFormulaLoc f `H.And` compileTCasLoc cas av) bs
compileTCasLoc (CasLeaf Nothing)            av                         = H.T
compileTCasLoc (CasLeaf (Just (TEnum n)))   av                         = H.EqConst av (enumToInt n)
compileTCasLoc (CasLeaf (Just (TUInt _ i))) av                         = H.EqConst av (fromInteger i)
compileTCasLoc (CasLeaf (Just (TSInt _ i))) av                         = H.EqConst av (fromInteger i)
compileTCasLoc (CasLeaf (Just t))           av | (isInt $ termType t)  = H.EqVar   av (getAbsVar $ AVarInt t)
compileTCasLoc (CasLeaf (Just t))           av | (isEnum $ termType t) = H.EqVar   av (getAbsVar $ AVarEnum t)

compileFormulaLoc :: (?spec::Spec, ?emap::EMap f e c, ?loc::Loc, ?acfa::ACFA) => Formula -> TAST f e c
compileFormulaLoc FTrue                = H.T
compileFormulaLoc FFalse               = H.F
compileFormulaLoc (FBinOp Conj f1 f2)  = compileFormulaLoc f1 `H.And`  compileFormulaLoc f2
compileFormulaLoc (FBinOp Disj f1 f2)  = compileFormulaLoc f1 `H.Or`   compileFormulaLoc f2
compileFormulaLoc (FBinOp Impl f1 f2)  = compileFormulaLoc f1 `H.Imp`  compileFormulaLoc f2
compileFormulaLoc (FBinOp Equiv f1 f2) = compileFormulaLoc f1 `H.XNor` compileFormulaLoc f2
compileFormulaLoc (FNot f)             = H.Not $ compileFormulaLoc f
compileFormulaLoc (FBoolAVar av)       = H.Var $ getAbsVar av
compileFormulaLoc (FEq av1 av2)        = H.EqVar (getAbsVar av1) (getAbsVar av2)
compileFormulaLoc (FEqConst av c)      = H.EqConst (getAbsVar av) c

getAbsVar :: (?emap::EMap f e c, ?loc::Loc, ?acfa::ACFA) => AbsVar -> TASTVar f e
getAbsVar av = (fst ?emap) M.! (defloc, av)
    where defloc = case G.lab ?acfa ?loc of
                        Nothing          -> ?loc
                        Just (_, defmap) -> {-trace ("getAbsVar " ++ show av ++ " at " ++ show ?loc) $-} defmap M.! av

compileFormula :: (?spec::Spec) => Formula -> TAST f e c
compileFormula f = let ?loc  = cfaInitLoc in
                   let vmap = foldl' (\m v -> M.insert (?loc, v) (H.NVar $ avarBAVar v) m) M.empty (fAbsVars f) in
                   let ?emap = (vmap, M.empty)
                       ?acfa = G.empty
                   in compileFormulaLoc f

compileFCas :: (?spec::Spec) => FCascade -> TASTVar f e -> TAST f e c
compileFCas cas av = let ?loc  = cfaInitLoc in
                     let vmap = foldl' (\m v -> M.insert (?loc, v) (H.NVar $ avarBAVar v) m) M.empty (ecasAbsVars $ fmap formToExpr cas) in
                     let ?emap = (vmap, M.empty)
                         ?acfa = G.empty
                     in compileFCasLoc (fmap Just cas) (av, Iff)

compileTCas :: (?spec::Spec) => TCascade -> TASTVar f e -> TAST f e c
compileTCas cas av = let ?loc  = cfaInitLoc in
                     let vmap = foldl' (\m v -> M.insert (?loc, v) (H.NVar $ avarBAVar v) m) M.empty (ecasAbsVars $ fmap termToExpr cas) in
                     let ?emap = (vmap, M.empty)
                         ?acfa = G.empty
                     in compileTCasLoc (fmap Just cas) av
