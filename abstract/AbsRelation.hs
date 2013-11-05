module AbsRelation () where

import IRelation
import Predicate
import IExpr
import ISpec

type RelInst f e c = (Predicate, [TAST f e c])

instantiateRelation :: (?spec::Spec, ?pred::[Predicate]) => Relation -> [Expr] -> RelInst
instantiateRelation Relation{..} args = (p, asts)
    where
    p = mkPredicate (PUserRel relName, args)
    substs = zip (map fst relArgs) args
    asts = map (\r -> let cfa' = cfaMapExpr (exprSubstVar substs) r
                      in compileACFA [] $ tranCFAToACFA [] (finalLoc cfa') cfa') relRules
