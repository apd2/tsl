{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module RelationInline(relToIRel) where

import qualified Data.Map as M
import Control.Monad.State

import Relation
import RelationOps
import Inline
import Statement
import Expr
import Ops
import Spec
import ExprInline
import StatementInline
import NS
import Name
import Pos
import qualified IRelation as I
import qualified IVar      as I
import qualified IExpr     as I
import qualified ISpec     as I
import qualified CFA       as I

relToIRel :: (?spec::Spec) => Relation -> NameGen I.Relation 
relToIRel rel = do
    let relArgs = let ?scope = ScopeTemplate tmMain in map (\a -> (sname a, mkType $ typ a)) $ relArg rel
        -- Variable map used to compile rules.  One var per argument.
        lmap = M.fromList $ map (\a -> (name a, I.EVar $ sname a)) $ relArg rel
        ruleToCFA :: Expr -> NameGen I.CFA
        ruleToCFA e = do 
            let stat0 = SAssume nopos Nothing $ EBinOp nopos Eq (ERel nopos (name rel) $ map (ETerm nopos . return . name) $ relArg rel) e
            stat <- let ?scope = ScopeTemplate tmMain 
                    in statSimplify stat0
            let ctx = CFACtx { ctxEPID    = Nothing
                             , ctxStack   = [(ScopeTemplate tmMain, error $ "return from relation", Nothing, lmap)]
                             , ctxCFA     = I.newCFA (ScopeTemplate tmMain) stat I.true
                             , ctxBrkLocs = error "break outside a loop"
                             , ctxGNMap   = globalNMap
                             , ctxLastVar = 0
                             , ctxVar     = []
                             , ctxLabels  = []}
                ctx' = let ?procs = []
                           ?nestedmb = False
                       in execState (procStatToCFA stat I.cfaInitLoc) ctx        
            return $ ctxCFA ctx'
    relRules <- mapM ruleToCFA $ relRule rel
    return $ I.Relation {relName = sname rel,..}


--applyToIApply :: (?spec::Spec) => Apply -> I.Apply
--applyToIApply 
