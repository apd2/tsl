{-# LANGUAGE ImplicitParams #-}

module ExprOps(evalInt) where

import Scope
import Expr
import Spec

evalInt :: (?spec::Spec) => Scope -> ConstExpr -> Integer
evalInt = error "evalInt not implemented"

--validateExpr :: (?spec::Spec, MonadError String me) => Scope -> Expr -> me ()
--validateExpr s (ETerm   {epos::Pos, ssym::StaticSym})
--ELit    {epos::Pos, width::(Maybe Int), rad::Radix, ival::Integer}
--EBool   {epos::Pos, bval::Bool}
--EApply  {epos::Pos, mref::MethodRef, args::[Expr]}
--EField  {epos::Pos, struct::Expr, field::Ident}
--EPField {epos::Pos, struct::Expr, field::Ident}
--EIndex  {epos::Pos, arr::Expr, idx::Expr}
--EUnOp   {epos::Pos, uop::UOp, arg1::Expr}
--EBinOp  {epos::Pos, bop::BOp, arg1::Expr, arg2::Expr}
--ETernOp {epos::Pos, arg1::Expr, arg2::Expr, arg3::Expr}
--ECase   {epos::Pos, caseexpr::Expr, cases::[(Expr, Expr)], def::(Maybe Expr)}
--ECond   {epos::Pos, cases::[(Expr, Expr)], def::(Maybe Expr)}
--ESlice  {epos::Pos, slexpr::Expr, slice::Slice}
--EStruct {epos::Pos, typename::StaticSym, fields::(Either [(Ident, Expr)] [Expr])} -- either named or anonymous list of fields
--ENonDet {epos::Pos}
--
