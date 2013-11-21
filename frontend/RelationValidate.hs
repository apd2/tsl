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
import ExprInline
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
                         assert (isBool rl)            (pos rl) "Relation interpretation must be a boolean expression"
                         assert (exprNoSideEffects rl) (pos rl) "Relation interpretation must be a side-effect-free expression"
                         assert (isPureExpr rl)        (pos rl) "Relation interpretation must be a pure expression"
                         assert (exprIsSimple rl)      (pos rl) "Rule expression too complex" -- makes sure we do not need to constuct a CFA when inlining rule expression
                         return ()) relRule
    return ()
