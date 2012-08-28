{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module StatementOps(validateStat,
                    validateStat') where

import Control.Monad.Error
import Data.Maybe

import TSLUtil
import Pos
import Name
import Expr
import {-# SOURCE #-} ExprOps
import Spec
import NS
import Statement
import TypeSpec
import TypeSpecOps
import Var
import VarOps
import Method

validateStat :: (?spec::Spec, MonadError String me) => Scope -> Statement -> me ()
validateStat s e = let ?scope = s 
                   in validateStat' False e

-- Validating statements
-- * all loops
-- * method invocations
--   - if the method is a task, then the current context must be a process or task
--   - no recursion

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
