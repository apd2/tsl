{-# LANGUAGE ImplicitParams #-}

module ACFACompile(ACFA(..),
                   compileACFA,
                   compileFormula,
                   tcasAbsVars,
                   fcasAbsVars,
                   acasAbsVars) where

import qualified Data.Graph.Inductive as G
import qualified Data.Map             as M
import GHC.Exts
import Data.List
import Data.Maybe

import Util
import qualified HAST.HAST as H
import Cascade
import Predicate
import BFormula
import ISpec
import IType
import CFA
import Ops

-- Abstract variable assignment cascade.  Leaves are either terms or formulas
type ACascade = Either (Cascade Term) (Cascade Formula)

acasAbsVars :: (?spec::Spec) => ACascade -> [AbsVar]
acasAbsVars (Left cas)  = tcasAbsVars cas
acasAbsVars (Right cas) = fcasAbsVars cas

disj []  = H.F
disj [x] = x
disj xs  = H.Disj xs

conj []  = H.T
conj [x] = x
conj xs  = H.Conj xs


-- Abstract CFA - has the same topology as CFA, but labels transitions
-- with variable update functions and states--with sets of abstract
-- vars defined in the state
type ACFA = G.Gr [AbsVar] (Int,[ACascade])

data ASTAbsVar = CurAbsVar AbsVar
               | NxtAbsVar AbsVar

type TASTVar e = H.ASTVar () e ASTAbsVar
type TAST e    = H.AST () e e ASTAbsVar


compileACFA :: (?spec::Spec, ?pred::[Predicate]) => ACFA -> TAST e
compileACFA acfa = 
    let ord = sortBy (\l1 l2 ->   if' (elem l2 $ G.reachable l1 acfa) LT
                                $ if' (elem l1 $ G.reachable l2 acfa) GT
                                $ compare (delta l1) (delta l2))
              $ G.nodes acfa
              where delta l = G.outdeg acfa l - G.indeg acfa l
    in let ?acfa = acfa in mkAST ord

-- map of existentially quantified variables
-- * the first component of the tuple stores an existential variable
--   per each location and AbsVar defined in this location.
-- * the second component stores a variable per location and outgoing transition
type EMap e = (M.Map (Loc, AbsVar) (TASTVar e),
               M.Map (Loc, Int)    (TASTVar e))

mkAST :: (?spec::Spec, ?acfa::ACFA) => [Loc] -> TAST e
mkAST ord = mkAST' (M.empty, M.empty) ord

mkAST' :: (?spec::Spec,?acfa::ACFA) => EMap e -> [Loc] -> TAST e
mkAST' emap []          = H.T
mkAST' (vmap, tmap) ord = 
    H.Exists 1 
    $ (\fl -> H.existsMany (replicate (length out) 1)
              $ (\fll -> if null fll
                            then (mkAST' (vmap, tmap) $ tail ord) `H.And`
                                 (H.EqConst (H.EVar fl) 1)        `H.And` 
                                 mkFanin (vmap, tmap) fl 
                            else let tmap' = foldl' (\m (v, (_, (id,_))) -> M.insert (l,id) (H.EVar v) m) tmap $ zip fll out in
                                 H.existsMany (map avarWidth vs)
                                 $ (\xs -> let vmap' = foldl' (\m (v, av) -> M.insert (l,av) (H.EVar v) m) vmap $ zip xs vs
                                           in (mkAST' (vmap', tmap') $ tail ord)                                                   `H.And` 
                                              ((H.EqConst (H.EVar fl) 1) `H.XNor` (disj $ map (\x -> H.EqConst (H.EVar x) 1) fll)) `H.And`
                                              mkFanin (vmap', tmap') fl)))
    where 
    l   = head ord
    vs  = fromJust $ G.lab  ?acfa l
    out = G.lsuc ?acfa l
    mkFanin emap fl = conj $ map (\(l', tr) -> compileTransition emap l' l tr fl) $ G.lpre ?acfa l

formAbsVars :: (?spec::Spec) => Formula -> [AbsVar]
formAbsVars FTrue                     = []
formAbsVars FFalse                    = []
formAbsVars (FBinOp _ f1 f2)          = formAbsVars f1 ++ formAbsVars f2         
formAbsVars (FNot f)                  = formAbsVars f
formAbsVars (FPred p@(PAtom _ t1 t2)) = case typ t1 of
                                             Bool   -> termAbsVars t1 ++ termAbsVars t2
                                             Enum _ -> termAbsVars t1 ++ termAbsVars t2
--                                             UInt 1 -> termAbsVars t1 ++ termAbsVars t2
                                             _      -> [AVarPred p]

fcasAbsVars :: (?spec::Spec) => FCascade -> [AbsVar]
fcasAbsVars (CasLeaf f)  = formAbsVars f
fcasAbsVars (CasTree bs) = concatMap (\(f,c) -> formAbsVars f ++ fcasAbsVars c) bs

tcasAbsVars :: (?spec::Spec) => TCascade -> [AbsVar]
tcasAbsVars (CasLeaf t)  = termAbsVars t
tcasAbsVars (CasTree bs) = concatMap (\(f,c) -> formAbsVars f ++ tcasAbsVars c) bs

termAbsVars :: (?spec::Spec) => Term -> [AbsVar]
termAbsVars (TEnum _)   = []
termAbsVars TTrue       = []
termAbsVars (TUInt _ _) = []
termAbsVars (TSInt _ _) = []
termAbsVars t           = [AVarTerm t]


compileTransition :: (?spec::Spec, ?acfa::ACFA) => EMap e -> Loc -> Loc -> (Int, [ACascade]) -> e -> TAST e
compileTransition emap from to (idx, upd) tovar = trvar `H.XNor` (updast `H.And` (H.EqConst (H.EVar tovar) 1))
    where trvar  = H.EqConst ((snd emap) M.! (from, idx)) 1
          tovs   = fromJust $ G.lab ?acfa to
          updast = let ?emap = emap
                       ?from = from
                       ?to = to in
                   conj $ map compileTransition1 $ zip upd tovs

compileTransition1 :: (?spec::Spec, ?acfa::ACFA, ?emap::EMap e, ?from::Loc, ?to::Loc) => (ACascade, AbsVar) -> TAST e
compileTransition1 (cas, av) = 
    let astvar = case M.lookup (?to, av) (fst ?emap) of
                      Nothing -> H.NVar $ NxtAbsVar av
                      Just v  -> H.EVar v in
    let ?loc = ?from
    in case cas of
            Right fcas -> compileFCas fcas astvar
            Left  tcas -> compileTCas tcas astvar

compileFCas :: (?spec::Spec, ?acfa::ACFA, ?emap::EMap e, ?loc::Loc) => FCascade -> TASTVar e -> TAST e
compileFCas (CasLeaf f)  av = (H.EqConst av 1) `H.XNor` compileFormula f
compileFCas (CasTree bs) av = disj $ map (\(f,cas) -> compileFormulaLoc f `H.And` compileFCas cas av) bs

compileTCas :: (?spec::Spec, ?acfa::ACFA, ?emap::EMap e, ?loc::Loc) => TCascade -> TASTVar e -> TAST e
compileTCas (CasTree bs)          av = disj $ map (\(f,cas) -> compileFormulaLoc f `H.And` compileTCas cas av) bs
compileTCas (CasLeaf (TEnum n))   av = H.EqConst av (enumToInt n)
compileTCas (CasLeaf (TUInt _ i)) av = H.EqConst av (fromInteger i)
compileTCas (CasLeaf (TSInt _ i)) av = H.EqConst av (fromInteger i)
compileTCas (CasLeaf t)           av = H.EqVar   av (getTermVar t)

compileFormulaLoc :: (?spec::Spec, ?emap::EMap e, ?loc::Loc) => Formula -> TAST e
compileFormulaLoc FTrue                      = H.T
compileFormulaLoc FFalse                     = H.F
compileFormulaLoc (FBinOp Conj f1 f2)        = compileFormulaLoc f1 `H.And`  compileFormulaLoc f2
compileFormulaLoc (FBinOp Disj f1 f2)        = compileFormulaLoc f1 `H.Or`   compileFormulaLoc f2
compileFormulaLoc (FBinOp Impl f1 f2)        = compileFormulaLoc f1 `H.Imp`  compileFormulaLoc f2
compileFormulaLoc (FBinOp Equiv f1 f2)       = compileFormulaLoc f1 `H.XNor` compileFormulaLoc f2
compileFormulaLoc (FNot f)                   = H.Not $ compileFormulaLoc f
compileFormulaLoc (FPred p@(PAtom op t1 t2)) =
    case typ t1 of
         Bool   -> let t1' = compileBoolTerm t1
                       t2' = compileBoolTerm t2
                   in case op of 
                           REq  -> t1' `H.XNor` t2'
                           RNeq -> t1' `H.XOr`  t2'
         Enum _ -> case (t1,t2) of
                        (TEnum n1, TEnum n2) -> if (n1 == n2) && (op == REq) || (n1 /= n2) && (op == RNeq)
                                                   then H.T
                                                   else H.F
                        (TEnum n1, _)        -> let v2 = getTermVar t2
                                                    r  = H.EqConst v2 (enumToInt n1)
                                                in case op of
                                                        REq  -> r
                                                        RNeq -> H.Not r
                        (_, TEnum n2)        -> let v1 = getTermVar t1
                                                    r  = H.EqConst v1 (enumToInt n2)
                                                in case op of
                                                        REq  -> r
                                                        RNeq -> H.Not r
                        (_,_)                -> let v1 = getTermVar t1
                                                    v2 = getTermVar t2
                                                    r  = H.EqVar v1 v2
                                                in case op of 
                                                        REq  -> r
                                                        RNeq -> H.Not r
--         UInt 1 -> case (t1,t2) of
--                        (TUInt _ n1, TUInt _ n2) -> do let res = if (n1 == n2) 
--                                                                    then C.bone ?m 
--                                                                    else C.bzero ?m
--                                                       lift $ C.ref res
--                                                       return res
--                        (TUInt _ n1, _)          -> do v2 <- getTermVar t2
--                                                       r <- lift $ C.eqConst ?m v2 n1 
--                                                       return $ case op of
--                                                                     REq  -> r
--                                                                     RNeq -> C.bnot r
--                        (_, TUInt _ n2)        -> do v1 <- getTermVar t1
--                                                     r <- lift $ C.eqConst ?m v1 n2
--                                                     return $ case op of
--                                                                   REq  -> r
--                                                                   RNeq -> C.bnot r
--                        (_,_)                -> do v1 <- getTermVar t1
--                                                   v2 <- getTermVar t2
--                                                   r <- lift $ C.eqVars ?m v1 v2
--                                                   return $ case op of 
--                                                                 REq  -> r
--                                                                 RNeq -> C.bnot r
         _      -> getPredVar p

compileBoolTerm :: (?spec::Spec, ?emap::EMap e, ?loc::Loc) => Term -> TAST e
compileBoolTerm TTrue = H.T
compileBoolTerm t     = H.EqConst (getTermVar t) 1

getTermVar :: (?emap::EMap e, ?loc::Loc) => Term -> TASTVar e
getTermVar t = (fst ?emap) M.! (?loc, AVarTerm t)

getPredVar :: (?emap::EMap e, ?loc::Loc) => Predicate -> TAST e
getPredVar p = H.EqConst ((fst ?emap) M.! (?loc, AVarPred p)) 1

compileFormula :: (?spec::Spec) => Formula -> TAST e
compileFormula f = let ?loc  = cfaInitLoc 
                       ?emap = (M.empty, M.empty)
                   in compileFormulaLoc f
