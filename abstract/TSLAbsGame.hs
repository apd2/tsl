{-# LANGUAGE ImplicitParams #-}

module TSLAbsGame(tslAbsGame,
                  bexprToFormula) where

import Prelude hiding (and)
import Control.Monad.State
import Control.Applicative
import Data.Maybe
import Data.List hiding (and)
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

import Util hiding (trace)
import Ops
import qualified CuddExplicitDeref as C
import qualified BDDHelpers        as C
import ISpec
import TranSpec
import IExpr hiding (disj)
import IType
import CFA
import Cascade
import Predicate
import BFormula
import FCompile
import Inline
import qualified Interface   as Abs
import qualified TermiteGame as Abs

-----------------------------------------------------------------------
-- Interface
-----------------------------------------------------------------------

tslAbsGame :: Spec -> C.STDdManager s u -> Abs.Abstractor s u AbsVar AbsVar
tslAbsGame spec m = Abs.Abstractor { Abs.goalAbs   = tslGoalAbs   spec m
                                   , Abs.fairAbs   = tslFairAbs   spec m
                                   , Abs.initAbs   = tslInitAbs   spec m
                                   , Abs.contAbs   = tslContAbs   spec m
                                   --, gameConsistent  = tslGameConsistent  spec
                                   , Abs.updateAbs = tslUpdateAbs spec m
                                   }

tslGoalAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslGoalAbs spec m ops = do
    mapM (\g -> do let ?spec = spec
                       ?ops  = ops
                       ?m    = m
                   tranPrecondition (goalCond g))
         $ tsGoal $ specTran spec

tslFairAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslFairAbs spec m ops = do
    let ?spec = spec
        ?ops  = ops
        ?m    = m
    mapM bexprAbstract $ tsFair $ specTran spec

tslInitAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslInitAbs spec m ops = do 
    let ?spec = spec
        ?ops  = ops
        ?m    = m
    pre   <- tranPrecondition (fst $ tsInit $ specTran spec)
    extra <- bexprAbstract (snd $ tsInit $ specTran spec)
    res   <- lift $ C.band m pre extra
    lift $ C.deref m pre 
    lift $ C.deref m extra
    return res

-- TODO: where should this go?

--tslGameConsistent :: Spec -> C.STDdManager s u -> PDB s u (C.DDNode s u)
--tslGameConsistent spec m = do
--    let ?m = m
--    -- Enum vars can take values between 0 and n-1 (where n is the size of the enumeration)
--    evars  <- pdbGetEnumVars
--    constr <- mapM (\(av,sz) -> do v <- pdbGetVar av
--                                   constrs <- lift $ mapM (C.eqConst m v) [0..sz-1]
--                                   res <- lift $ C.disj m constrs
--                                   lift $ mapM (C.deref m) constrs
--                                   return res) 
--                   $ M.toList evars
--    res <- lift $ C.conj m constr
--    lift $ mapM (C.deref m) constr
--    return res

tslContAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslContAbs spec m ops = do 
    let ?spec = spec
        ?ops  = ops
        ?m    = m
    bexprAbstract $ mkContVar === true

tslUpdateAbs :: Spec -> C.STDdManager s u -> [(AbsVar,[C.DDNode s u])] -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslUpdateAbs spec m avars ops = do
    trace ("tslUpdateAbs " ++ (intercalate "," $ map (show . fst) avars)) $ return ()
    let ?spec = spec
        ?ops  = ops
        ?m    = m

    -- controllable
    cont <- do pervarfs <- varUpdateTrans avars $ tsCTran $ specTran spec
               cont <- lift $ C.conj m pervarfs
               _ <- lift $ mapM (C.deref m) pervarfs
               return cont

    -- uncontrollable
    ucont <- do updatefs <- mapM (varUpdateTrans avars) $ tsUTran $ specTran spec
                pervarfs <- lift $ mapM (C.disj m) $ transpose updatefs
                _ <- lift $ mapM (mapM (C.deref m)) updatefs
                ucont <- lift $ C.conj m pervarfs
                _ <- lift $ mapM (C.deref m) pervarfs
                return ucont
    update <- lift $ C.disj m [cont,ucont]
    lift $ C.deref m cont
    lift $ C.deref m ucont
    return update

----------------------------------------------------------------------------
-- PDB operations
----------------------------------------------------------------------------

pdbPred :: (?ops::PVarOps pdb s u) => PDB pdb s u [Predicate]
pdbPred = do
    bavars <- Abs.allVars ?ops
    return $ map (\(AVarPred p) -> p)
           $ filter avarIsPred 
           $ map bavarAVar bavars

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

----------------------------------------------------------------------------
-- Computing abstraction
----------------------------------------------------------------------------

bexprAbstract :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => Expr -> PDB pdb s u (C.DDNode s u)
bexprAbstract e = do
    p <- pdbPred
    let ?pred = p
    compileFormula $ bexprToFormula e

-- Convert boolean expression (possibly with pointers) to a formula without
-- introducing new pointer predicates.
bexprToFormula :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Formula
bexprToFormula e = fcasToFormula $ fmap bexprToFormula' $ exprExpandPtr e

-- Convert boolean expression (possibly with pointers) to a formula, 
-- introducing new pointer predicates if needed.
bexprToFormulaPlus :: (?spec::Spec, ?pred::[Predicate], ?m::C.STDdManager s u) => Expr -> Formula
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

-- Convert boolean expression without pointers to a formula
bexprToFormula' :: (?spec::Spec) => Expr -> Formula
bexprToFormula' e@(EVar _)                         = fAtom REq (exprToTerm e) TTrue
bexprToFormula'   (EConst (BoolVal True))          = FTrue
bexprToFormula'   (EConst (BoolVal False))         = FFalse
bexprToFormula' e@(EField _ _)                     = fAtom REq (exprToTerm e) TTrue
bexprToFormula' e@(EIndex _ _)                     = fAtom REq (exprToTerm e) TTrue
bexprToFormula'   (EUnOp Not e)                    = fnot $ bexprToFormula' e
bexprToFormula'   (EBinOp op e1 e2) | isRelBOp op  = combineExpr (bopToRelOp op) e1 e2
bexprToFormula'   (EBinOp op e1 e2) | isBoolBOp op = FBinOp (bopToBoolOp op) (bexprToFormula' e1) (bexprToFormula' e2)

combineExpr :: (?spec::Spec) => RelOp -> Expr -> Expr -> Formula
combineExpr REq  (EUnOp AddrOf e1) (EUnOp AddrOf e2) = combineAddrOfExpr e1 e2
combineExpr RNeq (EUnOp AddrOf e1) (EUnOp AddrOf e2) = fnot $ combineAddrOfExpr e1 e2
combineExpr op e1 e2 | typ e1 == Bool                = 
   case e1 of
       EConst (BoolVal True)  -> if op == REq then bexprToFormula' e2 else fnot $ bexprToFormula' e2
       EConst (BoolVal False) -> if op == REq then fnot $ bexprToFormula' e2 else bexprToFormula' e2
       _                      -> 
           case e2 of
                EConst (BoolVal True)  -> if op == REq then bexprToFormula' e1 else fnot $ bexprToFormula' e1
                EConst (BoolVal False) -> if op == REq then fnot $ bexprToFormula' e1 else bexprToFormula' e1
                _                      -> let f = FBinOp Equiv (bexprToFormula' e1) (bexprToFormula' e2)
                                          in if op == REq then f else fnot f
                     | otherwise                     = fAtom op (exprToTerm e1) (exprToTerm e2)

-- Two addrof expressions are equal if they are isomorphic and
-- array indices in matching positions in these expressions are equal.
combineAddrOfExpr :: (?spec::Spec) => Expr -> Expr -> Formula
combineAddrOfExpr (EVar n1)      (EVar n2)      | n1 == n2 = FTrue
combineAddrOfExpr (EVar n1)      (EVar n2)      | n1 /= n2 = FFalse
combineAddrOfExpr (EField e1 f1) (EField e2 f2) | f1 == f2 = combineAddrOfExpr e1 e2
                                                | f1 /= f2 = FFalse
combineAddrOfExpr (EIndex a1 i1) (EIndex a2 i2)            = fconj [combineAddrOfExpr a1 a2, combineExpr REq i1 i2]
combineAddrOfExpr (ESlice e1 s1) (ESlice e2 s2) | s1 == s2 = combineAddrOfExpr e1 e2
                                                | s1 /= s2 = FFalse
combineAddrOfExpr _              _                         = FFalse

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

----------------------------------------------------------------------------
-- Predicate/variable update functions
----------------------------------------------------------------------------

-- Cache of variable update functions for intermediate locations inside a transition:
-- [a] is the list of variable update functions, 
-- [AbsVar] is the list of variables that these functions depend on (these variable must 
-- be recomputed at the next iteration)
type Cache s u = M.Map Loc ([C.DDNode s u],[AbsVar])

cacheDeref :: (?m::C.STDdManager s u) => Cache s u -> PDB pdb s u ()
cacheDeref cache = do
    _ <- lift $ mapM (C.deref ?m) $ concatMap fst $ M.elems cache
    return ()

cacheRefLoc :: Cache s u -> Loc -> PDB pdb s u ()
cacheRefLoc cache loc = do
    _ <- lift $ mapM C.ref $ fst $ cache M.! loc
    return ()

-- Compute precondition of transition, i.e., variable
-- update function for empty set of variables
tranPrecondition :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => Transition -> PDB pdb s u (C.DDNode s u)
tranPrecondition tran = do
    cache <- varUpdateLoc [] (tranFrom tran) (tranCFA tran) (M.singleton (tranTo tran) ([C.bone ?m],[]))
    cacheRefLoc cache (tranTo tran)
    return $ head $ fst $ cache M.! (tranFrom tran)

-- Compute update functions for a list of variables wrt to a transition
varUpdateTrans :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => [(AbsVar,[C.DDNode s u])] -> Transition -> PDB pdb s u [C.DDNode s u]
varUpdateTrans vs t = do
    -- Main transition
    cache <- varUpdateLoc vs (tranFrom t) (tranCFA t) M.empty

    --return $ fst $ cache M.! tranFrom t

    -- Always-block
    let at = tsAlways $ specTran ?spec

    cacheA <- do -- prefill cache with the result computed for the main transition
                 cacheRefLoc cache (tranFrom t)
                 let prefill = M.singleton (tranTo at) (cache M.! tranFrom t)
                 cacheA <- varUpdateLoc vs (tranFrom at) (tranCFA at) prefill
                 cacheDeref cache
                 return cacheA

    -- Wire update transition
    let wt = tsWire $ specTran ?spec

    cacheW <- do -- prefill cache with the result computed for the always transition
                 cacheRefLoc cacheA (tranFrom at)
                 let prefill = M.singleton (tranTo wt) (cacheA M.! tranFrom at)
                 cacheW <- varUpdateLoc vs (tranFrom wt) (tranCFA wt) prefill
                 cacheDeref cacheA
                 return cacheW

    cacheRefLoc cacheW (tranFrom wt)
    cacheDeref cacheW
    return $ fst $ cacheW M.! tranFrom wt

-- Compute update functions for a list of variables for a location inside
-- transition CFA.  Record the result in a cache that will be used to recursively
-- compute update functions for predecessor locations.
varUpdateLoc :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => [(AbsVar,[C.DDNode s u])] -> Loc -> CFA -> Cache s u -> PDB pdb s u (Cache s u)
varUpdateLoc vs loc cfa cache | M.member loc cache    = return cache
                              | null (cfaSuc loc cfa) = do
    let avs = map fst vs
    rels <- mapM compileVar vs
    return $ M.insert loc (rels, avs) cache
                              | otherwise             = do
    -- Compute update functions in all successor locations
    cache' <- foldM (\c (_,loc') -> varUpdateLoc vs loc' cfa c) cache (cfaSuc loc cfa)
    -- Compute update functions for each outgoing transition
    rels <- mapM (\(s, loc') -> varUpdateStat s (cache' M.! loc')) (cfaSuc loc cfa)
    -- Aggregate results
    let avs = S.toList $ S.fromList $ concatMap snd rels
    bdds <- lift $ mapM (C.disj ?m) $ transpose $ map fst rels
    _ <- lift $ mapM (C.deref ?m) $ concatMap fst rels
    return $ M.insert loc (bdds, avs) cache'

-- Compute variable update functions for an individual statement
varUpdateStat :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => TranLabel -> ([C.DDNode s u], [AbsVar]) -> PDB pdb s u ([C.DDNode s u],[AbsVar])
varUpdateStat (TranStat (SAssume e)) (rels, vs) = do
    p <- pdbPred
    let ?pred = p
    let f = bexprToFormulaPlus e
        vs' = formAbsVars f
    rel <- compileFormula f
    fs  <- lift $ mapM (C.band ?m rel) rels
    lift $ C.deref ?m rel
    return (fs, S.toList $ S.fromList $ vs ++ vs')

varUpdateStat (TranStat (SAssign e1 e2)) (rels, vs) = 
    foldM (varUpdateAsnStat1 e1 e2) (rels,[]) vs

varUpdateStat _ (rels, vs) = do
    _ <- lift $ mapM C.ref rels
    return (rels,vs)

-- Given a list of variable update relations computed so far and  
-- assignment statement, recompute individual abstract variable and 
-- substitute the expression for it to all relations.
varUpdateAsnStat1 :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => Expr -> Expr -> ([C.DDNode s u], [AbsVar]) -> AbsVar -> PDB pdb s u ([C.DDNode s u],[AbsVar])
varUpdateAsnStat1 lhs rhs (rels, vs) av = do
    pr <- pdbPred
    let ?pred = pr
    case av of
         (AVarPred p) -> do let repl = updatePredAsn lhs rhs p
                                vs'  = formAbsVars repl
                            rels' <- mapM (\r -> formSubst r av repl) rels
                            return (rels', S.toList $ S.fromList $ vs ++ vs')
         (AVarTerm t) -> do let repl = casMap exprExpandPtr 
                                       $ updateScalAsn lhs rhs t
                            case typ t of
                                 Bool -> do let frepl = fcasToFormula $ fmap bexprToFormula' repl
                                                vs' = formAbsVars frepl
                                            --trace ("varUpdateAsnStat1(" ++ show av ++ ", " ++ (intercalate "," $ map show vs) ++ ") " ++ show lhs ++ ":=" ++ show rhs ++ " = " ++ show frepl) $ return ()
                                            rels' <- mapM (\r -> formSubst r av frepl) rels
                                            return (rels', S.toList $ S.fromList $ vs ++ vs')
                                 _    -> do let trepl = fmap exprToTerm repl
                                                vs'  = tcasAbsVars trepl
                                            rels' <- mapM (\r -> tcasSubst r av trepl) rels
                                            return (rels', S.toList $ S.fromList $ vs ++ vs')
 
-- Predicate update by assignment statement
updatePredAsn :: (?spec::Spec, ?pred::[Predicate], ?m::C.STDdManager s u) => Expr -> Expr -> Predicate -> Formula
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
