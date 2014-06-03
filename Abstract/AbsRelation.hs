{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module Abstract.AbsRelation (RelInst,
                    instantiateRelation) where

import Debug.Trace

import Ops
import Internal.IRelation
import Abstract.Predicate
import Internal.IExpr
import Internal.ISpec
import Abstract.MkPredicate

type RelInst = (Predicate, [(LogicOp, Expr)])

-- Assumes that all dereference operations have already been expanded
instantiateRelation :: (?spec::Spec) => Relation -> [Expr] -> RelInst
instantiateRelation Relation{..} args = {- trace ("instantiateRelation " ++ relName ++ show args ++ " = " ++ show rls)-} (p, rls)
    where
    p@PRel{..} = mkPRel relName args
    substs = zip (map fst relArgs) pArgs
    rls = map (\Rule{..} -> (ruleOp, mapExpr exprSubst ruleExpr)) relRules

    exprSubst :: Expr -> Expr
    exprSubst e@(EVar v)          = case lookup v substs of
                                         Nothing -> e
                                         Just e' -> e'
    exprSubst e@(EConst _)        = e
    exprSubst   (EField e f)      = EField (exprSubst e) f
    exprSubst   (EIndex a i)      = case exprSubst a of
                                         ERange a' (f, _) -> EIndex a' (plusmod a' [f, exprSubst i])
                                         a'               -> EIndex a' (exprSubst i)
    exprSubst   (ERange a (f, l)) = case exprSubst a of
                                         ERange a' (f', _) -> ERange a' (plusmod a' [exprSubst f,f'], exprSubst l)
                                         a'                -> ERange a' (exprSubst f, exprSubst l)
    exprSubst   (ELength a)       = let ERange _ (_, l') = exprSubst a
                                    in l'
    exprSubst   (EUnOp op e)      = EUnOp op (exprSubst e)
    exprSubst   (EBinOp op e1 e2) = EBinOp op (exprSubst e1) (exprSubst e2)
    exprSubst   (ESlice e s)      = exprSlice (exprSubst e) s
    exprSubst   (ERel n as)       = ERel n $ map exprSubst as
