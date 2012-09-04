{-# LANGUAGE ImplicitParams #-}

module ExprInline(tmpName,
                  exprSimplify) where

import TSLUtil
import NS
import Pos
import Name
import Spec
import Expr
import Statement

tmpName :: Pos -> Uniq -> Ident
tmpName p u = Ident p $ "$" ++ (show $ getUniq u)

exprSimplify :: (?spec::Spec, ?scope::Scope, ?uniq::Uniq) => Expr -> ([Statement], Expr)
exprSimplify = undefined


