{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module RelationInline(relToIRel,
                      applyToIApply) where

import qualified Data.Map as M
import Control.Monad.State

import Relation
import RelationOps
import Inline
import Statement
import Expr
import Spec
import ExprInline
import NS
import Name
import Pos
import qualified IRelation as I
import qualified IExpr     as I
import qualified CFA       as I

relToIRel :: (?spec::Spec) => Relation -> I.Relation 
relToIRel rel = 
    let relArgs = let ?scope = ScopeTemplate tmMain in map (\a -> (sname a, mkType $ typ a)) $ relArg rel
        -- Variable map used to compile rules.  One var per argument.
        lmap = M.fromList $ map (\a -> (name a, I.EVar $ sname a)) $ relArg rel
        ruleToIExpr :: Expr -> I.Expr
        ruleToIExpr e =  
            let sc = ScopeRelation tmMain rel
                (_,e1) = let ?scope = sc in evalState (exprSimplify e) (0,[])
                ctx = CFACtx { ctxEPID    = Nothing
                             , ctxStack   = [(sc, error $ "return from relation", Nothing, lmap)]
                             , ctxCFA     = I.newCFA sc (SAssume nopos Nothing e1) I.true
                             , ctxBrkLocs = error "break outside a loop"
                             , ctxGNMap   = globalNMap
                             , ctxLastVar = 0
                             , ctxVar     = []
                             , ctxLabels  = []}
            in let ?procs = []
                   ?nestedmb = False
               in evalState (exprToIExprDet e1) ctx        
        relRules = map ruleToIExpr $ relRule rel
    in I.Relation {relName = sname rel,..}


applyToIApply :: (?spec::Spec) => Apply -> I.Apply
applyToIApply Apply{..} = I.Apply (sname applyRel) $ map aargToIExpr applyArg

aargToIExpr :: (?spec::Spec) => Expr -> I.Expr
aargToIExpr e = evalState (exprToIExprDet e) ctx
    -- no simplification should be required
    where ctx = CFACtx { ctxEPID    = Nothing
                       , ctxStack   = [(ScopeTemplate tmMain, error $ "return from apply argument", Nothing, M.empty)]
                       , ctxCFA     = I.newCFA (ScopeTemplate tmMain) (SSeq nopos Nothing []) I.true
                       , ctxBrkLocs = error "break outside a loop"
                       , ctxGNMap   = globalNMap
                       , ctxLastVar = 0
                       , ctxVar     = []
                       , ctxLabels  = []}
