{-# LANGUAGE ImplicitParams #-}

module FCompile (formAbsVars,
                 tcasAbsVars,
                 compileVar,
                 compileFormula,
                 tcasSubst,
                 formSubst) where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.ST

import qualified CuddExplicitDeref as C
import qualified BDDHelpers        as C
import ISpec
import qualified Interface         as Abs
import Cascade
import Predicate
import BFormula
import IType
import IVar

formAbsVars :: (?spec::Spec) => Formula -> [AbsVar]
formAbsVars FTrue                     = []
formAbsVars FFalse                    = []
formAbsVars (FBinOp _ f1 f2)          = formAbsVars f1 ++ formAbsVars f2         
formAbsVars (FNot f)                  = formAbsVars f
formAbsVars (FPred p@(PAtom _ t1 t2)) = case typ t1 of
                                             Bool   -> termAbsVars t1 ++ termAbsVars t2
                                             Enum _ -> termAbsVars t1 ++ termAbsVars t2
                                             _      -> [AVarPred p]

tcasAbsVars :: (?spec::Spec) => TCascade -> [AbsVar]
tcasAbsVars (CasLeaf t)  = termAbsVars t
tcasAbsVars (CasTree bs) = concatMap (\(f,c) -> formAbsVars f ++ tcasAbsVars c) bs

termAbsVars :: (?spec::Spec) => Term -> [AbsVar]
termAbsVars (TEnum _) = []
termAbsVars TTrue     = []
termAbsVars t         = [AVarTerm t]

mkTermVar :: (?spec::Spec, ?ops::PVarOps pdb s u) => Term -> PDB pdb s u [C.DDNode s u]
mkTermVar t = do
    (Abs.getVar ?ops) $ case termCategory t of 
                             VarTmp   -> Abs.LabelVar (AVarTerm t) (termWidth t)
                             VarState -> Abs.StateVar (AVarTerm t) (termWidth t)

mkPredVar :: (?spec::Spec, ?ops::PVarOps pdb s u) => Predicate -> PDB pdb s u (C.DDNode s u)
mkPredVar p = do
    liftM head
    $ (Abs.getVar ?ops) $ case predCategory p of 
                               VarTmp   -> Abs.LabelVar (AVarPred p) 1
                               VarState -> Abs.StateVar (AVarPred p) 1

pdbGetAVar :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => AbsVar -> PDB pdb s u [C.DDNode s u]
pdbGetAVar (AVarTerm t) = mkTermVar t
pdbGetAVar (AVarPred p) = liftM (\x -> [x]) $ mkPredVar p 

-- Compile _existing_ abstract var
compileVar :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => (AbsVar,[C.DDNode s u]) -> PDB pdb s u (C.DDNode s u)
compileVar (av,v') = do 
    v <- pdbGetAVar av
    lift $ C.eqVars ?m v v'

compileBoolTerm :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => Term -> PDB pdb s u (C.DDNode s u)
compileBoolTerm TTrue = return $ C.bone ?m

compileBoolTerm t = liftM head $ mkTermVar t

compileFormula :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => Formula -> PDB pdb s u (C.DDNode s u)
compileFormula FTrue             = do lift $ C.ref $ C.bone ?m
                                      return $ C.bone ?m
compileFormula FFalse            = do lift $ C.ref $ C.bzero ?m
                                      return $ C.bzero ?m
compileFormula (FBinOp op f1 f2) = do 
    f1' <- compileFormula f1
    f2' <- compileFormula f2
    res <- case op of
                Conj  -> lift $ C.band  ?m f1' f2'
                Disj  -> lift $ C.bor   ?m f1' f2'
                Impl  -> lift $ C.bimp  ?m f1' f2'
                Equiv -> lift $ C.bxnor ?m f1' f2'
    lift $ C.deref ?m f1'
    lift $ C.deref ?m f2'
    return res

compileFormula (FNot f)          = do
    f' <- compileFormula f
    return $ C.bnot f'

compileFormula (FPred p@(PAtom op t1 t2)) =
    case typ t1 of
         Bool   -> do t1' <- compileBoolTerm t1
                      t2' <- compileBoolTerm t2
                      case op of 
                           REq  -> lift $ C.bxnor ?m t1' t2'
                           RNeq -> lift $ C.bxor  ?m t1' t2'
         Enum _ -> case (t1,t2) of
                        (TEnum n1, TEnum n2) -> do let res = if (n1 == n2) 
                                                                then C.bone ?m 
                                                                else C.bzero ?m
                                                   lift $ C.ref res
                                                   return res
                        (TEnum n1, _)        -> do v2 <- mkTermVar t2
                                                   r <- lift $ C.eqConst ?m v2 (enumToInt n1)
                                                   return $ case op of
                                                                 REq  -> r
                                                                 RNeq -> C.bnot r
                        (_, TEnum n2)        -> do v1 <- mkTermVar t1
                                                   r <- lift $ C.eqConst ?m v1 (enumToInt n2)
                                                   return $ case op of
                                                                 REq  -> r
                                                                 RNeq -> C.bnot r
                        (_,_)                -> do v1 <- mkTermVar t1
                                                   v2 <- mkTermVar t2
                                                   r <- lift $ C.eqVars ?m v1 v2
                                                   return $ case op of 
                                                                 REq  -> r
                                                                 RNeq -> C.bnot r
         _      -> do v <- mkPredVar p
                      lift $ C.ref v
                      return v


compileTCas :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => TCascade -> [C.DDNode s u] -> PDB pdb s u (C.DDNode s u)
compileTCas (CasLeaf (TEnum n)) v = lift $ C.eqConst ?m v (enumToInt n)
compileTCas (CasLeaf t)         v = do 
    vt <- mkTermVar t
    lift $ C.eqVars ?m v vt
compileTCas (CasTree bs)        v = do
    fs <- mapM (\(f,cas) -> do f' <- compileFormula f
                               cas' <- compileTCas cas v
                               res <- lift $ C.band ?m f' cas'
                               lift $ C.deref ?m f'
                               lift $ C.deref ?m cas'
                               return res) bs
    res <- lift $ C.disj ?m fs
    _ <- lift $ mapM (C.deref ?m) fs
    return res


-- Substitute variable av in relation rel with a formula
-- Computed as: exists v' . rel' /\ (v' <-> f), where v' is 
-- an auxiliary temp variable and rel' is rel with variable v 
-- substituted by v'.
formSubst :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => C.DDNode s u -> AbsVar -> Formula -> PDB pdb s u (C.DDNode s u)
formSubst rel av f = 
    (Abs.withTmp ?ops)
    $ (\v' -> do v    <- pdbGetAVar av
                 rel' <- lift $ C.shift ?m v [v'] rel
                 f'   <- compileFormula f
                 eq   <- lift $ C.bxnor ?m v' f'
                 lift $ C.deref ?m f'
                 con  <- lift $ C.band ?m rel' eq
                 lift $ C.deref ?m rel'
                 lift $ C.deref ?m eq
                 --cube <- lift $ C.conj ?m v'
                 cube <- lift $ C.nodesToCube ?m [v']
                 res  <- lift $ C.bexists ?m con cube
                 lift $ C.deref ?m cube
                 lift $ C.deref ?m con
                 -- check that res does not depend on v'
                 support <- lift $ C.supportIndices ?m res
                 supcubes <- lift $ mapM (\i -> C.indicesToCube ?m [i]) support
                 if any (== v') supcubes
                    then error $ "formSubst: tmp variable in result"
                    else do _ <- lift $ mapM (C.deref ?m) supcubes
                            return res)

-- Substitute variable av with cascade cas in relation rel.
-- Computed as follows:
-- Replace each term t in cascade with (t == av') and compile the
-- resulting cascade, yielding relation f'.  
-- Substitute v with v' in rel, yielding rel'.
-- Return: exists v' . rel' /\ f'
tcasSubst :: (?spec::Spec, ?ops::PVarOps pdb s u, ?m::C.STDdManager s u) => C.DDNode s u -> AbsVar -> TCascade -> PDB pdb s u (C.DDNode s u)
tcasSubst rel av cas = 
    withTmpMany ?ops (avarWidth av)
    $ (\v' -> do v    <- pdbGetAVar av
                 rel' <- lift $ C.shift ?m v v' rel
                 f'   <- compileTCas cas v'
                 con  <- lift $ C.band ?m rel' f'
                 lift $ C.deref ?m rel'
                 lift $ C.deref ?m f'
                 cube <- lift $ C.conj ?m v'
                 res  <- lift $ C.bexists ?m con cube
                 lift $ C.deref ?m cube
                 lift $ C.deref ?m con
                 -- check that res does not depend on v'
                 support <- lift $ C.supportIndices ?m res
                 supcubes <- lift $ mapM (\i -> C.indicesToCube ?m [i]) support
                 if any (\d -> elem d v') supcubes
                    then error $ "tcasSubst: tmp variable in result"
                    else do _ <- lift $ mapM (C.deref ?m) supcubes
                            return res)


withTmpMany :: Abs.VarOps pdb v s u -> Int -> ([C.DDNode s u] -> StateT pdb (ST s) a) -> StateT pdb (ST s) a
withTmpMany ops n f = withTmpMany' ops [] n f

withTmpMany' :: Abs.VarOps pdb v s u -> [C.DDNode s u] -> Int -> ([C.DDNode s u] -> StateT pdb (ST s) a) -> StateT pdb (ST s) a
withTmpMany' _   nodes 0 f = f nodes
withTmpMany' ops nodes n f = (Abs.withTmp ops) (\node -> withTmpMany' ops (node:nodes) (n-1) f)
