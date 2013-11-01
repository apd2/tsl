{-# LANGUAGE RecordWildCards, ImplicitParams #-}

module RelationValidate(validateRelation,
                        validateApply) where

import Control.Monad.Error

import TSLUtil
import Pos
import Relation
import Template
import Spec
import Name
import Type
import NS
import TypeValidate
import ExprValidate
import ExprOps
import TypeOps
import RelationOps

validateRelation :: (?spec::Spec, MonadError String me) => Template -> Relation -> me ()
validateRelation tm r@Relation{..} = do 
    -- argument names are unique
    uniqNames (\n -> "Argument " ++ n ++ " declared multiple times in relation " ++ sname r) relArg
    let ?privoverride = False
    -- validate argument types
    _ <- mapM (\a -> case tspec a of
                          StructSpec _ _ -> err (pos $ tspec a) "Inline struct declaration is illegal in relation argument" -- because then there is no way to pass such an argument by value
                          _              -> return ())
              relArg
    _ <- mapM (\a -> do validateTypeSpec (ScopeTemplate tm)  $ tspec a
                        validateTypeSpec2 (ScopeTemplate tm) $ tspec a) relArg
    -- validate rule expressions
    _ <- mapM (validateExpr (ScopeRelation tm r)) relRule
    _ <- mapM (\rl -> do let ?scope = ScopeRelation tm r 
                         assert (isBool rl) (pos rl) "Relation interpretation must be a boolean expression"
                         assert (exprNoSideEffectsWithPtr rl) (pos rl) "Relation interpretation must be a side-effect-free expression"
                         return ()) relRule
    return ()

validateApply :: (?spec::Spec, MonadError String me) => Template -> Apply -> me ()
validateApply tm a@Apply{..} = do
    let ?privoverride = False
    -- Relation name refers to a valid relation
    (_, r@Relation{..}) <- checkRelation (ScopeTemplate tm) applyRel
    -- Argument list has correct length
    assert (length applyArg == length relArg) (pos a) $ "Relation " ++ sname r ++ " is defined with " ++ show (length relArg) ++ 
                                                        " arguments, but is instantiated with " ++ show (length applyArg) ++ " arguments" 
    -- Relation arguments are 
    -- * valid expressions
    -- * of matching types
    -- * L-expressions or constant expressions
    _ <- mapM (\(aa, ra) -> do validateExpr (ScopeTemplate tm) aa
                               let ?scope = ScopeTemplate tm
                               checkTypeMatch aa ra
                               assert (isLExpr aa || isConstExpr aa) (pos aa) "apply arguments must be L-expressions or constant expressions")
         $ zip applyArg relArg
    return ()
