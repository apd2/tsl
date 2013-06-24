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
import GHC.Exts

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
import Inline
import qualified Interface   as Abs
import qualified TermiteGame as Abs
import qualified HAST.HAST   as H
import ACFA
import ACFACompile

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
    p <- pdbPred
    let ?spec = spec
        ?ops  = ops
        ?m    = m
        ?pred = p
    mapM (\g -> do let ast = tranPrecondition (goalCond g)
                   H.compile ast)
         $ tsGoal $ specTran spec

tslFairAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslFairAbs spec m ops = do
    p <- pdbPred
    let ?spec = spec
        ?ops  = ops
        ?m    = m
        ?p    = pred
    mapM (H.compile . bexprAbstract . fairCond) $ tsFair $ specTran spec

tslInitAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslInitAbs spec m ops = do 
    p <- pdbPred
    let ?spec = spec
        ?ops  = ops
        ?m    = m
        ?pred = p
    let pre   = tranPrecondition (fst $ tsInit $ specTran spec)
        extra = bexprAbstract (snd $ tsInit $ specTran spec)
        res   = H.And pre extra
    H.compile res

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
    p <- pdbPred
    let ?spec = spec
        ?ops  = ops
        ?m    = m
        ?pred = p
    H.compile $ bexprAbstract $ mkContVar === true

tslUpdateAbs :: Spec -> C.STDdManager s u -> [(AbsVar,[C.DDNode s u])] -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslUpdateAbs spec m avars ops = do
    trace ("tslUpdateAbs " ++ (intercalate "," $ map (show . fst) avars)) $ return ()
    p <- pdbPred
    let ?spec = spec
        ?ops  = ops
        ?m    = m
        ?pred = p
    let cont  = varUpdateTrans avars $ tsCTran $ specTran spec
        ucont = H.Disj $ map (varUpdateTrans avars) $ tsUTran $ specTran spec
    H.compile $ H.Or cont ucont

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

bexprAbstract :: (?spec::Spec, ?pred::[Predicate]) => Expr -> TAST
bexprAbstract = compileFormula . bexprToFormula

-- Convert boolean expression (possibly with pointers) to a formula without
-- introducing new pointer predicates.
bexprToFormula :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Formula
bexprToFormula e = fcasToFormula $ fmap bexprToFormula' $ exprExpandPtr e

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

-- Compute precondition of transition without taking always blocks and wires into account
tranPrecondition :: (?spec::Spec, ?pred::[Predicate]) => Transition -> TAST e
tranPrecondition tran = varUpdateLoc [] (tranFrom t) (tranCFA t)

-- Compute update functions for a list of variables wrt to a transition
varUpdateTrans :: (?spec::Spec, ?pred::[Predicate]) => [AbsVar] -> Transition -> TAST e
varUpdateTrans vs t = varUpdateLoc vs (tranFrom t) (cfaLocInlineWireAlways ?spec (tranCFA t) (tranFrom t))

-- Compute update functions for a list of variables for a location inside
-- transition CFA. 
varUpdateLoc :: (?spec::Spec, ?pred::[Predicate]) => [AbsVar] -> Loc -> CFA -> TAST e
varUpdateLoc vs loc cfa = compileACFA $ tranCFAToACFA vs loc cfa
