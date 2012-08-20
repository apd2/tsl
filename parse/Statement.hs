module Statement(Statement(SVarDecl,SReturn,SSeq,SPar,SForever,SDo,
                           SWhile,SFor,SChoice,SPause,SStop,SBreak,SInvoke,
                           SAssert,SAssume,SAssign,SITE,SCase,SMagic),
                 stmtVar) where

import Data.Maybe
import Text.PrettyPrint

import PP
import Pos
import Name
import Expr
import Var

-- Statements
data Statement = SVarDecl {stpos::Pos, svar::Var}
               | SReturn  {stpos::Pos, retval::Expr}
               | SSeq     {stpos::Pos, statements::[Statement]}
               | SPar     {stpos::Pos, statements::[Statement]}
               | SForever {stpos::Pos, body::Statement}
               | SDo      {stpos::Pos, body::Statement, cond::Expr}
               | SWhile   {stpos::Pos, cond::Expr, body::Statement}
               | SFor     {stpos::Pos, limits::(Maybe Statement, Expr, Statement), body::Statement}
               | SChoice  {stpos::Pos, statements::[Statement]}
               | SPause   {stpos::Pos}
               | SStop    {stpos::Pos}
               | SBreak   {stpos::Pos}
               | SInvoke  {stpos::Pos, mname::MethodRef, args::[Expr]}
               | SAssert  {stpos::Pos, cond::Expr}
               | SAssume  {stpos::Pos, cond::Expr}
               | SAssign  {stpos::Pos, lhs::Expr, rhs::Expr}
               | SITE     {stpos::Pos, cond::Expr, sthen::Statement, selse::(Maybe Statement)}     -- if () then {..} [else {..}]
               | SCase    {stpos::Pos, caseexpr::Expr, cases::[(Expr, Statement)], def::(Maybe Statement)}
               | SMagic   {stpos::Pos, magiccond::(Either Ident Expr)}
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
    pp (SBreak _)                   = text "break"
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
    pos       = stpos
    atPos s p = s{stpos = p}

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
