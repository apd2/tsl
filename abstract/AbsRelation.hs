module AbsRelation () where

type RelInst f e c = (Predicate, [TAST f e c])

instantiateRelation :: (?spec::Spec) => Relation -> [Expr] -> RelInst
instantiateRelation rel args = 
    
