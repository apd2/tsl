{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module StatementOps(mapStat,
                    statMapExpr,
                    statMapTSpec,
                    statCallees,
                    statFlatten,
                    validateStat,
                    validateStat') where

import Control.Monad.Error
import Data.Maybe

import TSLUtil
import Pos
import Name
import Expr
import {-# SOURCE #-} ExprOps
import ExprFlatten
import ExprValidate
import Spec
import NS
import Statement
import Type
import TypeOps
import Var
import VarOps
import Method
import Template
import InstTree

-- Map function over all substatements
mapStat :: (?spec::Spec) => (Scope -> Statement -> Statement) -> Scope -> Statement -> Statement
mapStat f s (SSeq     p ss)        = f s $ SSeq     p (map (mapStat f s) ss)
mapStat f s (SPar     p ss)        = f s $ SPar     p (map (mapStat f s) ss)
mapStat f s (SForever p b)         = f s $ SForever p (mapStat f s b)
mapStat f s (SDo      p b c)       = f s $ SDo      p (mapStat f s b) c
mapStat f s (SWhile   p c b)       = f s $ SWhile   p c (mapStat f s b)
mapStat f s (SFor     p (i,c,u) b) = f s $ SFor     p ((fmap (mapStat f s) i),c, mapStat f s u) (mapStat f s b)
mapStat f s (SChoice  p ss)        = f s $ SChoice  p (map (mapStat f s) ss)
mapStat f s (SITE     p c t me)    = f s $ SITE     p c (mapStat f s t) (fmap (mapStat f s) me)
mapStat f s (SCase    p c cs md)   = f s $ SCase    p c (map (\(e,st) -> (e,mapStat f s st)) cs) (fmap (mapStat f s) md)
mapStat f s st                     = f s st

-- Map function over all TypeSpec's in the statement
statMapTSpec :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Scope -> Statement -> Statement
statMapTSpec f s st = mapStat (statMapTSpec' f) s st

statMapTSpec' :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Scope -> Statement -> Statement
statMapTSpec' f s (SVarDecl p v) = SVarDecl p (Var (pos v) (mapTSpec f s $ tspec v) (name v) (varInit v))
statMapTSpec' _ _ st             = st

-- Map function over all expression in the statement
statMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> Statement -> Statement
statMapExpr f s st = mapStat (statMapExpr' f) s st

statMapExpr' :: (?spec::Spec) =>  (Scope -> Expr -> Expr) -> Scope -> Statement -> Statement
statMapExpr' f s (SVarDecl p v)         = SVarDecl p (varMapExpr f s v)
statMapExpr' f s (SReturn  p mr)        = SReturn  p (fmap (mapExpr f s) mr)
statMapExpr' f s (SDo      p b c)       = SDo      p b (mapExpr f s c)
statMapExpr' f s (SWhile   p c b)       = SWhile   p (mapExpr f s c) b
statMapExpr' f s (SFor     p (i,c,u) b) = SFor     p (i, mapExpr f s c, u) b
statMapExpr' f s (SInvoke  p m as)      = SInvoke  p m (map (mapExpr f s) as)
statMapExpr' f s (SAssert  p e)         = SAssert  p (mapExpr f s e)
statMapExpr' f s (SAssume  p e)         = SAssume  p (mapExpr f s e)
statMapExpr' f s (SAssign  p l r)       = SAssign  p (mapExpr f s l) (mapExpr f s r)
statMapExpr' f s (SITE     p c t me)    = SITE     p (mapExpr f s c) t me
statMapExpr' f s (SCase    p c cs md)   = SCase    p (mapExpr f s c) (map (mapFst $ mapExpr f s) cs) md
statMapExpr' f s (SMagic   p (Right e)) = SMagic   p (Right $ mapExpr f s e)
statMapExpr' f s st                     = st

-- Find all methods invoked by the statement
statCallees :: (?spec::Spec) => Scope -> Statement -> [(Pos, (Template, Method))]
statCallees s (SVarDecl _ v)            = fromMaybe [] $ fmap (exprCallees s) $ varInit v
statCallees s (SReturn  _ me)           = fromMaybe [] $ fmap (exprCallees s) me
statCallees s (SSeq     _ ss)           = concatMap (statCallees s) ss
statCallees s (SPar     _ ss)           = concatMap (statCallees s) ss
statCallees s (SForever _ b)            = statCallees s b
statCallees s (SDo      _ b c)          = statCallees s b ++ exprCallees s c
statCallees s (SWhile   _ c b)          = exprCallees s c ++ statCallees s b
statCallees s (SFor     _ (i,c,u) b)    = (fromMaybe [] $ fmap (statCallees s) i) ++ exprCallees s c ++ statCallees s u ++ statCallees s b
statCallees s (SChoice  _ ss)           = concatMap (statCallees s) ss
statCallees s (SInvoke  p mref as)      = (p,getMethod s mref):(concatMap (exprCallees s) as)
statCallees s (SAssert  _ e)            = exprCallees s e
statCallees s (SAssume  _ e)            = exprCallees s e
statCallees s (SAssign  _ l r)          = exprCallees s l ++ exprCallees s r
statCallees s (SITE     _ c t me)       = exprCallees s c ++ statCallees s t ++ (fromMaybe [] $ fmap (statCallees s) me)
statCallees s (SCase    _ c cs md)      = exprCallees s c ++ 
                                          concatMap (\(e,st) -> exprCallees s e ++ statCallees s st) cs ++
                                          (fromMaybe [] $ fmap (statCallees s) md)
statCallees _ _                         = []


statFlatten :: (?spec::Spec) => IID -> Scope -> Statement -> Statement
statFlatten iid s st = statMapExpr (exprFlatten iid) s st


validateStat :: (?spec::Spec, MonadError String me) => Scope -> Statement -> me ()
validateStat s e = let ?scope = s 
                   in validateStat' False e

-- The first argument indicates that the statement belongs to a loop
validateStat' :: (?spec::Spec, ?scope::Scope, MonadError String me) => Bool -> Statement -> me ()
validateStat' _ (SVarDecl p v) = do 
    validateVar ?scope v
    validateVar2 ?scope v

validateStat' _ (SReturn p me) = do
    case ?scope of
         ScopeMethod  _ m  -> case methRettyp m of
                                   Nothing -> assert (isNothing me) p "Cannot return value from method with void return type"
                                   Just t  -> do assert (isJust me) p "Return value not specified"
                                                 checkTypeMatch (Type ?scope t) (fromJust me)
         ScopeProcess _ pr -> assert (isNothing me) p "Cannot return value from a process"

validateStat' l (SSeq _ ss) = do
    mapM (validateStat' l) ss
    return ()

validateStat' l (SPar _ ss) = do
    mapM (validateStat' l) ss
    return ()

validateStat' _ (SForever _ b) = do
    checkLoopBody b

validateStat' _ (SDo _ b c) = do
    validateExpr' c
    assert (isBool c) (pos c) $ "Loop condition is not of boolean type"
    checkLoopBody b

validateStat' _ (SWhile _ c b) = do
    validateExpr' c
    assert (isBool c) (pos c) $ "Loop condition is not of boolean type"
    checkLoopBody b

validateStat' _ (SFor _ (mi, c, s) b) = do
    validateExpr' c
    assert (isBool c) (pos c) $ "Loop condition is not of boolean type"
    case mi of
         Just i  -> validateStat' False i
         Nothing -> return ()
    validateStat' False s
    checkLoopBody b

validateStat' l (SChoice _ ss) = do
    mapM (validateStat' l) ss
    return ()

validateStat' _ (SPause p) = do
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p $ "pause inside function"
                                  Procedure         -> err p $ "pause inside procedure"
                                  Task Controllable -> err p $ "pause inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ pr -> return ()

validateStat' _ (SStop p) = do
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p $ "stop inside function"
                                  Procedure         -> err p $ "stop inside procedure"
                                  Task Controllable -> err p $ "stop inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ pr -> return ()

validateStat' l (SBreak p) = assert l p $ "break outside a loop"
validateStat' _ (SInvoke p m as) = validateCall p m as
validateStat' _ (SAssert _ e) = do
    validateExpr' e
    assert (isBool e) (pos e) $ "Assertion must be a boolean expression"
    assert (exprNoSideEffects e) (pos e) $ "Assertion must be side-effect free"

validateStat' _ (SAssume _ e) = do
    validateExpr' e
    assert (isBool e) (pos e) $ "Assumption must be a boolean expression"
    assert (exprNoSideEffects e) (pos e) $ "Assumption must be side-effect free"

validateStat' _ (SAssign _ lhs rhs) = do
    validateExpr' lhs
    validateExpr' rhs
    assert (isLExpr lhs) (pos lhs) $ "Left-hand side of assignment is not an L-value"
    checkTypeMatch lhs rhs

validateStat' l (SITE _ i t e) = do
    validateExpr' i
    assert (isBool i) (pos i) $ "Condition of an if-statement must be a boolean expression"
    validateStat' l t
    case e of 
         Just s  -> validateStat' l s
         Nothing ->  return ()

validateStat' l (SCase p c cs md) = do
    validateExpr' c
    assert (length cs > 0) p $ "Empty case statement"
    mapM (\(e,s) -> do {validateExpr' e; validateStat' l s}) cs
    case md of
         Just d  -> validateStat' l d
         Nothing -> return ()
    mapM (\(e1,_) -> checkTypeMatch c e1) cs
    return ()

validateStat' l (SMagic p g) = do
    case ?scope of
         ScopeMethod t m -> case methCat m of
                                 Task Uncontrollable -> return ()
                                 _                   -> err p "Magic blocks only allowed in uncontrollable tasks"
         _               -> err p "Magic blocks only allowed in uncontrollable tasks"
    case g of
         Left n  -> do {checkGoal ?scope n; return()}
         Right e -> do validateExpr' e
                       assert (isBool e) (pos e) $ "Objective must be a boolean expression"

-- There is no path through the loop body that does not break out of the loop and
-- does not contain some form of pause
checkLoopBody :: (?spec::Spec, ?scope::Scope, MonadError String me) => Statement -> me ()
checkLoopBody s = do
    validateStat' True s
    return $ error "checkLoopBody not implemented"
