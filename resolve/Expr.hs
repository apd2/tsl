module Expr(Expr, ConstExpr, evalInt) where

data Expr = Expr
type ConstExpr = Expr

evalInt :: ConstExpr -> Integer
evalInt = error "evalInt not implemented"
