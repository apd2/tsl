{-# LANGUAGE ImplicitParams #-}

module ExprFlatten(exprFlatten, 
                   exprFlatten', 
                   flattenName,
                   unflattenName) where

import Data.List.Split

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
unflattenName n = map (Ident nopos) $ splitOn "::" (sname n)

exprFlatten :: (?spec::Spec) => IID -> Scope -> Expr -> Expr
exprFlatten iid s e = mapExpr (exprFlatten' iid) s e

exprFlatten' :: (?spec::Spec) => IID -> Scope -> Expr -> Expr
exprFlatten' iid s e@(ETerm p n) = case getTerm s n of
                                       ObjGVar _ v                           -> ETerm p [itreeFlattenName iid (name v)]
                                       ObjWire _ w                           -> ETerm p [itreeFlattenName iid (name w)]
                                       ObjEnum (Type (ScopeTemplate t) _) en -> ETerm p [flattenName t en]
                                       ObjConst (ScopeTemplate t) c          -> ETerm p [flattenName t c]
                                       _            -> e
exprFlatten' iid s (EField p e f) = 
    let ?scope = s
    in case tspec e of
            TemplateTypeSpec _ tn -> case objGet (ObjTemplate $ getTemplate tn) f of
                                          ObjGVar _ v -> ETerm p [itreeFlattenName (itreeRelToAbsPath iid (epath e)) (name v)]
                                          ObjWire _ w -> ETerm p [itreeFlattenName (itreeRelToAbsPath iid (epath e)) (name w)]
                                     where epath (ETerm _ n)     = n
                                           epath (EField _ e' n) = epath e' ++ [n]
            _                     -> EField p e f

exprFlatten' iid _ (EApply p (MethodRef p' n) as) = EApply p (MethodRef p' [itreeFlattenName (itreeRelToAbsPath iid (init n)) (last n)]) as
exprFlatten' iid _ (EAtLab p l)                   = EAtLab p $ itreeFlattenName iid l
exprFlatten' iid _ (ERel p n as)                  = ERel   p (itreeFlattenName iid n) as
exprFlatten' _   _ e                              = e
