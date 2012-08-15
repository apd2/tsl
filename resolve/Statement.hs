module Statement(Statement,
                 stmtVar) where

import Data.Maybe
import Text.PrettyPrint

import PP
import Pos
import Name
import Expr
import Var

-- Statements
data Statement = SVarDecl {spos::Pos, svar::Var}
               | SReturn  {spos::Pos, retval::Expr}
               | SSeq     {spos::Pos, statements::[Statement]}
               | SPar     {spos::Pos, statements::[Statement]}
               | SForever {spos::Pos, body::Statement}
               | SDo      {spos::Pos, body::Statement, cond::Expr}
               | SWhile   {spos::Pos, cond::Expr, body::Statement}
               | SFor     {spos::Pos, limits::(Maybe Statement, Expr, Statement), body::Statement}
               | SChoice  {spos::Pos, statements::[Statement]}
               | SPause   {spos::Pos}
               | SStop    {spos::Pos}
               | SInvoke  {spos::Pos, mname::MethodRef, args::[Expr]}
               | SAssert  {spos::Pos, cond::Expr}
               | SAssume  {spos::Pos, cond::Expr}
               | SAssign  {spos::Pos, lhs::Expr, rhs::Expr}
               | SITE     {spos::Pos, cond::Expr, sthen::Statement, selse::(Maybe Statement)}     -- if () then {..} [else {..}]
               | SCase    {spos::Pos, caseexpr::Expr, cases::[(Expr, Statement)], def::(Maybe Statement)}
               | SMagic   {spos::Pos, magiccond::(Either Ident Expr)}
instance PP Statement where
    pp (SVarDecl _ d)               = pp d
    pp (SReturn _ e)                = text "return" <+> pp e
    pp (SSeq _ ss)                  = braces' $ vcat $ map ((<> semi) . pp) ss
    pp (SPar _ ss)                  = text "fork" $+$ (braces' $ vcat $ map ((<> semi) . pp) ss)
    pp (SForever _ s)               = text "forever" $+$ pp s
    pp (SDo _ s cond)               = text "do" $+$ pp s <+> text "while" <+> (parens $ pp cond)
    pp (SWhile _ cond s)            = (text "while" <+> (parens $ pp cond)) $+$ pp s
    pp (SFor _ (init, cond, upd) s) = (text "for" <+> (parens $ pp init <> semi <+> pp cond <> semi <+> pp upd)) $+$ pp s
    pp (SChoice _ ss)               = text "choice" $+$ (braces' $ vcat $ map ((<> semi) . pp) ss)
    pp (SPause _)                   = text "pause"
    pp (SStop _)                    = text "stop"
    pp (SInvoke _ m args)           = pp m <+> (parens $ hsep $ punctuate comma $ map pp args)
    pp (SAssert _ e)                = text "assert" <+> (parens $ pp e)
    pp (SAssume _ e)                = text "assume" <+> (parens $ pp e)
    pp (SAssign _ l r)              = pp l <+> char '=' <+> pp r
    pp (SITE _ cond s1 ms2)         = text "if" <+> (parens $ pp cond) $+$ pp s1 $+$
                                      (case ms2 of
                                            Nothing -> empty
                                            Just s2 -> text "else" $+$ pp s2)
    pp (SCase _ e cases def)        = text "case" <+> (parens $ pp e) <+> (braces' $ ppcases $+$ ppdef)
                                           where ppcases = vcat $ map (\(c,s) -> pp c <> colon <+> pp s <> semi) cases
                                                 ppdef = case def of 
                                                              Nothing -> empty
                                                              Just s  -> text "default" <> colon <+> pp s <> semi
    pp (SMagic _ (Left g))          = (braces $ text "...") <+> text "using" <+> pp g
    pp (SMagic _ (Right c))         = (braces $ text "...") <+> text "post" <+> pp c

instance WithPos Statement where
    pos       = spos
    atPos s p = s{spos = p}

stmtVar :: Statement -> [Var]
stmtVar (SVarDecl _ v)          = [v]
stmtVar (SSeq _ ss)             = concat $ map stmtVar ss
stmtVar (SPar _ ss)             = concat $ map stmtVar ss
stmtVar (SForever _ s)          = stmtVar s
stmtVar (SDo _ s _)             = stmtVar s
stmtVar (SWhile _ _ s)          = stmtVar s
stmtVar (SFor _ (init,_,inc) s) = concat $ map stmtVar $ inc:s:(maybeToList init)               
stmtVar (SChoice _ ss)          = concat $ map stmtVar ss
stmtVar (SITE _ _ ts es)        = concat $ map stmtVar $ ts:(maybeToList es)
stmtVar (SCase _ _ cs def)      = concat $ map stmtVar $ (snd $ unzip cs) ++ (maybeToList def)
stmtVar _                       = []
