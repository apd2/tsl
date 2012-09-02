{-# LANGUAGE ImplicitParams #-}

module ExprFlatten(exprFlatten) where

import Name
import Expr
import {-# SOURCE #-} ExprOps
import InstTree
import TypeSpec
import Spec
import NS

exprFlatten :: (?spec::Spec) => IID -> Scope -> Expr -> Expr
exprFlatten iid s e = mapExpr (exprFlatten' iid)  s e

exprFlatten' iid s e@(ETerm p n) = case getTerm s n of
                                       ObjGVar tm v -> ETerm p [itreeFlattenName iid (name v)]
                                       _            -> e
exprFlatten' iid s (EField p e f) = 
    let ?scope = s
    in case tspec e of
            TemplateTypeSpec _ tn -> case objGet (ObjTemplate $ getTemplate tn) f of
                                          ObjGVar _ v -> ETerm p [itreeFlattenName (itreeRelToAbsPath iid (epath e)) (name v)]
                                          ObjWire _ w -> ETerm p [itreeFlattenName (itreeRelToAbsPath iid (epath e)) (name w)]
                                     where epath (ETerm _ n)    = n
                                           epath (EField _ e n) = epath e ++ [n]
            _                     -> EField p e f

exprFlatten' iid s (EApply p (MethodRef p' n) as) = EApply p (MethodRef p' [itreeFlattenName (itreeRelToAbsPath iid (init n)) (last n)]) as