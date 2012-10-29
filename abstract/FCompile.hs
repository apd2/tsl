{-# LANGUAGE ImplicitParams #-}

module FCompile (TAbsVar,
                 TmpVars,
                 PDB,
                 formAbsVars,
                 tcasAbsVars,
                 compileVar,
                 compileFormula,
                 tcasSubst,
                 formSubst) where

import qualified Data.Map as M

import ISpec
import PredicateDB
import Cascade
import Predicate
import Formula
import LogicClasses
import IType

type TAbsVar = AbsVar Predicate

type TmpVars v = M.Map TAbsVar v

type PDB c v x = PredicateDB c v Predicate (TmpVars v) x


formAbsVars :: (?spec::Spec) => Formula -> [TAbsVar]
formAbsVars FTrue                     = []
formAbsVars FFalse                    = []
formAbsVars (FBinOp _ f1 f2)          = formAbsVars f1 ++ formAbsVars f2         
formAbsVars (FNot f)                  = formAbsVars f
formAbsVars (FPred p@(PAtom _ t1 t2)) = case typ t1 of
                                             Bool   -> termAbsVars t1 ++ termAbsVars t2
                                             Enum _ -> termAbsVars t1 ++ termAbsVars t2
                                             _      -> [PredVar (show p) p]

tcasAbsVars :: (?spec::Spec) => TCascade -> [TAbsVar]
tcasAbsVars (CasLeaf t)  = termAbsVars t
tcasAbsVars (CasTree bs) = concatMap (\(f,c) -> formAbsVars f ++ tcasAbsVars c)bs

termAbsVars :: (?spec::Spec) => Term -> [TAbsVar]
termAbsVars (TEnum _) = []
termAbsVars TTrue     = []
termAbsVars t         = [termAbsVar t]

termAbsVar :: (?spec::Spec) => Term -> TAbsVar
termAbsVar t = case typ t of
                    Bool   -> BoolVar (show t)
                    Enum n -> EnumVar (show t) sz where sz = length $ enumEnums $ getEnum n

mkTermVar :: (AllOps c v a, ?spec::Spec) => Term -> PDB c v v
mkTermVar t = do
    tmap <- pdbGetExt
    (av,v) <- case typ t of
                   Bool -> do let av = BoolVar $ show t 
                              v <- pdbAllocVar av (termCategory t)
                              return (av,v)
                   (Enum n) -> do let e = getEnum n
                                      av = EnumVar (show t) (length $ enumEnums e)
                                  v <- pdbAllocVar av (termCategory t)
                                  return (av,v)
    case M.lookup av tmap of
         Nothing -> do v' <- pdbAllocTmpVar $ typeWidth t
                       let tmap' = M.insert av v' tmap
                       pdbPutExt tmap'
         Just v' -> return ()
    return v

mkPredVar :: (AllOps c v a, ?spec::Spec) => Predicate -> PDB c v v
mkPredVar p = do
    tmap <- pdbGetExt
    let av = PredVar (show p) p
    v <- pdbAllocVar av (predCategory p)
    case M.lookup av tmap of
         Nothing -> do v' <- pdbAllocTmpVar 1
                       let tmap' = M.insert av v' tmap
                       pdbPutExt tmap'
         Just v' -> return ()
    return v

-- Compile _existing_ abstract var
compileVar :: (AllOps c v a, ?spec::Spec) => (TAbsVar,v) -> PDB c v a
compileVar (av,v') = do 
    v <- pdbGetVar av
    m <- pdbCtx
    return $ eqVars m v v'

compileBoolTerm :: (AllOps c v a, ?spec::Spec) => Term -> PDB c v a
compileBoolTerm TTrue = do
    m <- pdbCtx
    return $ topOp m

compileBoolTerm t = do
    m <- pdbCtx
    v <- mkTermVar t
    return $ head $ compVar m v


compileFormula :: (AllOps c v a, ?spec::Spec) => Formula -> PDB c v a
compileFormula f = do
    m <- pdbCtx
    compileFormula' m f

compileFormula' :: (AllOps c v a, ?spec::Spec) => c -> Formula -> PDB c v a
compileFormula' m FTrue             = return $ topOp m
compileFormula' m FFalse            = return $ botOp m
compileFormula' m (FBinOp op f1 f2) = do 
    f1' <- compileFormula f1
    f2' <- compileFormula f2
    return $ case op of
                  Conj  -> andOp  m f1' f2'
                  Disj  -> orOp   m f1' f2'
                  Impl  -> impOp  m f1' f2'
                  Equiv -> xnorOp m f1' f2'
compileFormula' m (FPred p@(PAtom op t1 t2)) =
    case typ t1 of
         Bool   -> do t1' <- compileBoolTerm t1
                      t2' <- compileBoolTerm t2
                      return $ case op of 
                                    REq  -> xnorOp m t1' t2'
                                    RNeq -> xorOp  m t1' t2'
         Enum n -> case (t1,t2) of
                        (TEnum n1, TEnum n2) -> return $ if (n1 == n2) then topOp m else botOp m
                        (TEnum n1, _)        -> do v2 <- mkTermVar t2
                                                   let r = eqConst m v2 (enumToInt n1)
                                                   return $ case op of
                                                                 REq  -> r
                                                                 RNeq -> notOp m r
                        (_, TEnum n2)        -> do v1 <- mkTermVar t1
                                                   let r = eqConst m v1 (enumToInt n2)
                                                   return $ case op of
                                                                 REq  -> r
                                                                 RNeq -> notOp m r
                        (_,_)                -> do v1 <- mkTermVar t1
                                                   v2 <- mkTermVar t2
                                                   let r = eqVars m v1 v2
                                                   return $ case op of 
                                                                 REq  -> r
                                                                 RNeq -> notOp m r
         _      -> do v <- mkPredVar p
                      return $ head $ compVar m v 


compileTCas :: (AllOps c v a, ?spec::Spec) => TCascade -> v -> PDB c v a
compileTCas cas v = do
    m <- pdbCtx
    compileTCas' m cas v

compileTCas' :: (AllOps c v a, ?spec::Spec) => c -> TCascade -> v -> PDB c v a
compileTCas' m (CasLeaf (TEnum n)) v = return $ eqConst m v (enumToInt n)
compileTCas' m (CasLeaf t)         v = do 
    vt <- mkTermVar t
    return $ eqVars m v vt
compileTCas' m (CasTree bs)        v = do
    fs <- mapM (\(f,cas) -> do f' <- compileFormula f
                               cas' <- compileTCas' m cas v
                               return $ andOp m f' cas') bs
    return $ disjOp m fs


-- Substitute variable av in relation rel with a formula
-- Computed as: exists v' . rel' /\ (v' <-> f), where v' is 
-- an auxiliary temp variable and rel' is rel with variable v 
-- substituted by v'.
formSubst :: (AllOps c v a, ?spec::Spec) => a -> TAbsVar -> Formula -> PDB c v a
formSubst rel av f = do
    m    <- pdbCtx
    v    <- pdbGetVar av
    tmap <- pdbGetExt
    let v' = tmap M.! av
        cubev' = head $ compVar m v'
        rel' = swap m v v' rel
    f' <- compileFormula f
    return $ exists m v' $ andOp m rel' (xnorOp m cubev' f')

-- Substitute variable av with cascade cas in relation rel.
-- Computed as follows:
-- Replace each term t in cascade with (t == av') and compile the
-- resulting cascade, yielding relation f'.  
-- Substitu v with v' in rel, yielding rel'.
-- Return: exists v' . rel' /\ f'
tcasSubst :: (AllOps c v a, ?spec::Spec) => a -> TAbsVar -> TCascade -> PDB c v a
tcasSubst rel av cas = do
    m    <- pdbCtx
    v    <- pdbGetVar av
    tmap <- pdbGetExt
    let v' = tmap M.! av
        rel' = swap m v v' rel
    f' <- compileTCas cas v'
    return $ exists m v' $ andOp m rel' f'
