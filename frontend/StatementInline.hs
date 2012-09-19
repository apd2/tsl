{-# LANGUAGE ImplicitParams #-}

module StatementInline(statSimplify) where

import TSLUtil
import Spec
import Pos
import Name
import NS
import Statement
import Expr
import ExprOps
import Template
import Var
import Method
import Process
import Type
import ExprInline

import qualified ISpec as I

statSimplify :: (?spec::Spec, ?scope::Scope, ?uniq::Uniq) => Statement -> Statement
statSimplify s = sSeq (pos s) $ statSimplify' s

statSimplify' :: (?spec::Spec, ?scope::Scope, ?uniq::Uniq) => Statement -> [Statement]
statSimplify' (SVarDecl p v) = 
    case varInit v of
         Just e -> (SVarDecl p v{varInit = Nothing}) :
                   (statSimplify' $ SAssign p (ETerm (pos $ varName v) [varName v]) e)

statSimplify' (SReturn p (Just e)) = 
    let (ss,e') = exprSimplify e
    in ss ++ [SReturn p (Just e')]

statSimplify' (SSeq p ss)           = [SSeq p $ concatMap statSimplify' ss]
statSimplify' (SPar p ss)           = [SPar p $ map (mapSnd statSimplify) ss]
statSimplify' (SForever p s)        = [SForever p $ statSimplify s]
statSimplify' (SDo p b c)           = let (ss,c') = exprSimplify c
                                      in [SDo p (sSeq (pos b) $ statSimplify' b ++ ss) c']
statSimplify' (SWhile p c b)        = let (ss,c') = exprSimplify c
                                      in ss ++ [SWhile p c' (sSeq (pos b) $ statSimplify' b ++ ss)]
statSimplify' (SFor p (mi, c, s) b) = let i' = case mi of
                                                    Nothing -> []
                                                    Just i  -> statSimplify' i
                                          (ss,c') = exprSimplify c
                                          s' = statSimplify s
                                      in i' ++ ss ++ [SFor p (Nothing, c',s') (sSeq (pos b) $ statSimplify' b ++ ss)]
statSimplify' (SChoice p ss)        = [SChoice p $ map statSimplify ss]
statSimplify' (SInvoke p mref as)   = -- Order of argument evaluation is undefined in C;
                                      -- Go left-to-right
                                      let (ss, as') = unzip $ map exprSimplify as
                                      in (concat ss) ++ [SInvoke p mref $ as']
statSimplify' (SAssert p c)         = let (ss,c') = exprSimplify c
                                      in ss ++ [SAssert p c']
statSimplify' (SAssume p c)         = let (ss,c') = exprSimplify c
                                      in ss ++ [SAssume p c']
statSimplify' (SAssign p l r)       = -- Evaluate lhs first
                                      let (ssl,l') = exprSimplify l
                                          ssr = exprSimplifyAsn p l' r
                                      in ssl ++ ssr
statSimplify' (SITE p c t me)       = let (ss,c') = exprSimplify c
                                      in ss ++ [SITE p c' (statSimplify t) (fmap statSimplify me)]
statSimplify' (SCase p c cs md)     = -- Case labels must be side-effect-free, so it is ok to 
                                      -- evaluate them in advance
                                      let (ssc,c')   = exprSimplify c
                                          (sscs,clabs') = unzip $ map exprSimplify (fst $ unzip cs)
                                          cstats = map statSimplify (snd $ unzip cs)
                                      in (concat sscs) ++ ssc ++ [SCase p c' (zip clabs' cstats) (fmap statSimplify md)]
statSimplify' (SMagic p (Right e))  = let (ss,e') = exprSimplify e
                                      in (SMagic p (Right $ EBool (pos e) True)):(ss ++ [SAssert (pos e) e'])
statSimplify' st                    = [st]


