{-# LANGUAGE ImplicitParams #-}

module ExprFlatten(exprFlatten, 
                   exprFlatten', 
                   flattenName,
                   unflattenName) where

import Debug.Trace

import Name
import Expr
import {-# SOURCE #-} ExprOps
import InstTree
import Type
import Spec
import NS
import Template
import Pos

-- Flatten static enum or const name by prepending template name to it
flattenName :: (WithName a) => Template -> a -> Ident
flattenName t x = Ident (pos $ name x) $ (sname t) ++ "::" ++ (sname x)

unflattenName :: Ident -> StaticSym
unflattenName n = error "unflattenName not implemented"

exprFlatten :: (?spec::Spec) => IID -> Scope -> Expr -> Expr
exprFlatten iid s e = mapExpr (exprFlatten' iid) s e

exprFlatten' iid s e@(ETerm p n) = case getTerm s n of
                                       ObjGVar tm v                          -> ETerm p [itreeFlattenName iid (name v)]
                                       ObjEnum (Type (ScopeTemplate t) _) en -> ETerm p [flattenName t en]
                                       ObjConst (ScopeTemplate t) c          -> ETerm p [flattenName t c]
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

exprFlatten' _ _ e = e
