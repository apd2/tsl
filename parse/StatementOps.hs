{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module StatementOps() where

import Control.Monad.Error
import Data.Maybe

import TSLUtil
import Pos
import Name
import Expr
import ExprOps
import Spec
import NS
import Statement
import TypeSpec
import TypeSpecOps
import Var
import Method

validateStat :: (?spec::Spec, MonadError String me) => Scope -> Statement -> me ()
validateStat s e = let ?scope = s 
                   in validateStat' False e


-- Validating statements
-- * all loops
--   - there is no path through the loop body that does not break out of the loop and
--     does not contain some form of pause
-- * pause - only allowed inside an uncontrollable or invisible task or a process
-- * stop - only allowed inside an uncontrollable or invisible task or a process
-- * break - only allowed inside a loop
-- * method invocations
--   - method name refers to a visible method (local or exported)
--   - if the method is a task, then the current context must be a process or task
--   - the number and types of arguments match
--   - no recursion
-- * assert, assume arguments must be valid, side effect-free boolean expressions 
-- * assign: LHS is a valid l-value expression (in particular, it cannot be a continous 
--   assignment variable); RHS is a valid expression of a matching type
-- * if-then-else.  The conditional expression is of type bool
-- * case: the key expression and case clauses have matching types
-- * magic block: 
--   - only allowed in uncontrollable tasks
--   - valid goal name or boolean goal expression

-- The first argument indicates that the statement belongs to a loop
validateStat' :: (?spec::Spec, ?scope::Scope, MonadError String me) => Bool -> Statement -> me ()
validateStat' _ (SVarDecl p v) = do 
    validateTypeSpec ?scope (tspec v)
    case varInit v of
         Just e -> do validateExpr' e
                      checkTypeMatch (Type ?scope $ tspec v) e
         _      -> return ()

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
--               | SAssume  {stpos::Pos, cond::Expr}
--               | SAssign  {stpos::Pos, lhs::Expr, rhs::Expr}
--               | SITE     {stpos::Pos, cond::Expr, sthen::Statement, selse::(Maybe Statement)}     -- if () then {..} [else {..}]
--               | SCase    {stpos::Pos, caseexpr::Expr, cases::[(Expr, Statement)], def::(Maybe Statement)}
--               | SMagic   {stpos::Pos, magiccond::(Either Ident Expr)}
--

checkLoopBody :: (?spec::Spec, ?scope::Scope, MonadError String me) => Statement -> me ()
checkLoopBody s = do
    validateStat' True s
