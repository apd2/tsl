{-# LANGUAGE ImplicitParams #-}

module FCompile (TAbsVar,
                 TmpVars,
                 PDBPriv,
                 newPDBPriv,
                 PDB,
                 pdbGetEnumVars,
                 formAbsVars,
                 tcasAbsVars,
                 compileVar,
                 compileFormula,
                 tcasSubst,
                 formSubst) where

import qualified Data.Map as M
import Control.Monad.Trans

import qualified CuddExplicitDeref as C
import qualified BDDHelpers        as C
import TSLUtil
import ISpec
import PredicateDB
import Cascade
import Predicate
import BFormula
import LogicClasses
import IType

type TAbsVar = AbsVar Predicate

type TmpVars s u = M.Map TAbsVar [C.DDNode s u]
type EnumVars = M.Map TAbsVar Int

data PDBPriv s u = PDBPriv (TmpVars s u) EnumVars

newPDBPriv :: PDBPriv s u
newPDBPriv = PDBPriv M.empty M.empty

type PDB s u x = PredicateDB Predicate (PDBPriv s u) s u x

pdbGetEnumVars :: PDB s u EnumVars
pdbGetEnumVars = do
    PDBPriv _ e <- pdbGetExt
    return e

pdbGetTmpVars :: PDB s u (TmpVars s u)
pdbGetTmpVars = do
    PDBPriv t _ <- pdbGetExt
    return t

pdbPutTmpVars :: TmpVars s u -> PDB s u ()
pdbPutTmpVars t = do
    PDBPriv _ e <- pdbGetExt
    pdbPutExt $ PDBPriv t e

formAbsVars :: (?spec::Spec) => Formula -> [TAbsVar]
formAbsVars FTrue                     = []
formAbsVars FFalse                    = []
formAbsVars (FBinOp _ f1 f2)          = formAbsVars f1 ++ formAbsVars f2         
formAbsVars (FNot f)                  = formAbsVars f
formAbsVars (FPred p@(PAtom _ t1 t2)) = case typ t1 of
                                             Bool   -> termAbsVars t1 ++ termAbsVars t2
                                             Enum _ -> termAbsVars t1 ++ termAbsVars t2
                                             _      -> [PredVar p]

tcasAbsVars :: (?spec::Spec) => TCascade -> [TAbsVar]
tcasAbsVars (CasLeaf t)  = termAbsVars t
tcasAbsVars (CasTree bs) = concatMap (\(f,c) -> formAbsVars f ++ tcasAbsVars c)bs

termAbsVars :: (?spec::Spec) => Term -> [TAbsVar]
termAbsVars (TEnum _) = []
termAbsVars TTrue     = []
termAbsVars t         = [termAbsVar t]

termWidth :: (?spec::Spec) => Term -> Int
termWidth t = case typ t of
                   Bool   -> 1
                   Enum n -> bitWidth $ (length $ enumEnums $ getEnumeration n) - 1

termAbsVar :: (?spec::Spec) => Term -> TAbsVar
termAbsVar t = NonPredVar (show t) (termWidth t)

mkTermVar :: (?spec::Spec) => Term -> PDB s u [C.DDNode s u]
mkTermVar t = do
    PDBPriv tmap enums <- pdbGetExt
    let av = termAbsVar t
    v <- pdbAllocVar av (termCategory t)
    case M.lookup av tmap of
         Nothing -> do v' <- pdbAllocTmpVar $ termWidth t
                       let tmap' = M.insert av v' tmap
                           enums' = case typ t of
                                         Enum n -> M.insert av (length $ enumEnums $ getEnumeration n) enums
                                         _      -> enums
                       pdbPutExt $ PDBPriv tmap' enums'
         Just v' -> return ()
    return v

mkPredVar :: (?spec::Spec) => Predicate -> PDB s u [C.DDNode s u]
mkPredVar p = do
    tmap <- pdbGetTmpVars
    let av = PredVar p
    v <- pdbAllocVar av (predCategory p)
    case M.lookup av tmap of
         Nothing -> do v' <- pdbAllocTmpVar 1
                       let tmap' = M.insert av v' tmap
                       pdbPutTmpVars tmap'
         Just v' -> return ()
    return v

-- Compile _existing_ abstract var
compileVar :: (?spec::Spec) => (TAbsVar,[C.DDNode s u]) -> PDB s u (C.DDNode s u)
compileVar (av,v') = do 
    v <- pdbGetVar av
    m <- pdbCtx
    lift $ C.eqVars m v v'

compileBoolTerm :: (?spec::Spec) => Term -> PDB s u (C.DDNode s u)
compileBoolTerm TTrue = do
    m <- pdbCtx
    return $ C.bone m

compileBoolTerm t = do
    v <- mkTermVar t
    return $ head v


compileFormula :: (?spec::Spec) => Formula -> PDB s u (C.DDNode s u)
compileFormula f = do
    m <- pdbCtx
    compileFormula' m f

compileFormula' :: (?spec::Spec) => C.STDdManager s u -> Formula -> PDB s u (C.DDNode s u)
compileFormula' m FTrue             = do lift $ C.ref $ C.bone m
                                         return $ C.bone m
compileFormula' m FFalse            = do lift $ C.ref $ C.bzero m
                                         return $ C.bzero m
compileFormula' m (FBinOp op f1 f2) = do 
    f1' <- compileFormula f1
    f2' <- compileFormula f2
    res <- case op of
                Conj  -> lift $ C.band  m f1' f2'
                Disj  -> lift $ C.bor   m f1' f2'
                Impl  -> lift $ C.bimp  m f1' f2'
                Equiv -> lift $ C.bxnor m f1' f2'
    lift $ C.deref m f1'
    lift $ C.deref m f2'
    return res

compileFormula' m (FNot f)          = do
    f' <- compileFormula f
    return $ C.bnot f'

compileFormula' m (FPred p@(PAtom op t1 t2)) =
    case typ t1 of
         Bool   -> do t1' <- compileBoolTerm t1
                      t2' <- compileBoolTerm t2
                      case op of 
                           REq  -> lift $ C.bxnor m t1' t2'
                           RNeq -> lift $ C.bxor  m t1' t2'
         Enum n -> case (t1,t2) of
                        (TEnum n1, TEnum n2) -> do let res = if (n1 == n2) 
                                                                then C.bone m 
                                                                else C.bzero m
                                                   lift $ C.ref res
                                                   return res
                        (TEnum n1, _)        -> do v2 <- mkTermVar t2
                                                   r <- lift $ C.eqConst m v2 (enumToInt n1)
                                                   return $ case op of
                                                                 REq  -> r
                                                                 RNeq -> C.bnot r
                        (_, TEnum n2)        -> do v1 <- mkTermVar t1
                                                   r <- lift $ C.eqConst m v1 (enumToInt n2)
                                                   return $ case op of
                                                                 REq  -> r
                                                                 RNeq -> C.bnot r
                        (_,_)                -> do v1 <- mkTermVar t1
                                                   v2 <- mkTermVar t2
                                                   r <- lift $ C.eqVars m v1 v2
                                                   return $ case op of 
                                                                 REq  -> r
                                                                 RNeq -> C.bnot r
         _      -> do v <- mkPredVar p
                      let res = head v
                      lift $ C.ref res
                      return res


compileTCas :: (?spec::Spec) => TCascade -> [C.DDNode s u] -> PDB s u (C.DDNode s u)
compileTCas cas v = do
    m <- pdbCtx
    compileTCas' m cas v

compileTCas' :: (?spec::Spec) => C.STDdManager s u -> TCascade -> [C.DDNode s u] -> PDB s u (C.DDNode s u)
compileTCas' m (CasLeaf (TEnum n)) v = lift $ C.eqConst m v (enumToInt n)
compileTCas' m (CasLeaf t)         v = do 
    vt <- mkTermVar t
    lift $ C.eqVars m v vt
compileTCas' m (CasTree bs)        v = do
    fs <- mapM (\(f,cas) -> do f' <- compileFormula f
                               cas' <- compileTCas' m cas v
                               res <- lift $ C.band m f' cas'
                               lift $ C.deref m f'
                               lift $ C.deref m cas'
                               return res) bs
    res <- lift $ C.disj m fs
    lift $ mapM (C.deref m) fs
    return res


-- Substitute variable av in relation rel with a formula
-- Computed as: exists v' . rel' /\ (v' <-> f), where v' is 
-- an auxiliary temp variable and rel' is rel with variable v 
-- substituted by v'.
formSubst :: (?spec::Spec) => C.DDNode s u -> TAbsVar -> Formula -> PDB s u (C.DDNode s u)
formSubst rel av f = do
    m    <- pdbCtx
    v    <- pdbGetVar av
    tmap <- pdbGetTmpVars
    let v' = tmap M.! av
        cubev' = head v'
    --     rel' = swap m v v' rel
    rel' <- lift $ C.shift m v v' rel
    f'   <- compileFormula f
    eq   <- lift $ C.bxnor m cubev' f'
    lift $ C.deref m f'
    con  <- lift $ C.band m rel' eq
    lift $ C.deref m rel'
    lift $ C.deref m eq
    --cube <- lift $ C.conj m v'
    cube <- lift $ C.nodesToCube m v'
    res  <- lift $ C.bexists m con cube
    lift $ C.deref m cube
    lift $ C.deref m con
    return res

-- Substitute variable av with cascade cas in relation rel.
-- Computed as follows:
-- Replace each term t in cascade with (t == av') and compile the
-- resulting cascade, yielding relation f'.  
-- Substitu v with v' in rel, yielding rel'.
-- Return: exists v' . rel' /\ f'
tcasSubst :: (?spec::Spec) => C.DDNode s u -> TAbsVar -> TCascade -> PDB s u (C.DDNode s u)
tcasSubst rel av cas = do
    m    <- pdbCtx
    v    <- pdbGetVar av
    tmap <- pdbGetTmpVars
    let v' = tmap M.! av
    rel' <- lift $ C.shift m v v' rel
    f'   <- compileTCas cas v'
    con  <- lift $ C.band m rel' f'
    lift $ C.deref m rel'
    lift $ C.deref m f'
    cube <- lift $ C.conj m v'
    res  <- lift $ C.bexists m con cube
    lift $ C.deref m cube
    lift $ C.deref m con
    return res
