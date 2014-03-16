{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module CodeGen (gen1Step) where

import Interface
import TermiteGame
import BddRecord
import Predicate
import AbsSim
import ISpec hiding (getVar)
import Inline
import CG
import qualified IExpr             as I
import qualified CuddExplicitDeref as C

data Branch s u = BranchITE    (DDNode s u) (DDNode s u) (Branch s u)
                | BranchAction (DDNode s u) (DDNode s u)
                | BranchStuck  

-- A single synthesised step, consisting of a wait condition and
-- an if-then-else fork.
data Step s u = Step { stepWaitCond :: DDNode s u -- wait condition
                     , stepBranches :: Branch s u 
                     }

gen1Step :: Spec -> C.STDdManager s u -> RefineDynamic s u -> DB s u AbsVar AbsVar -> DDNode s u -> DDNode s u -> ST s (Step s u)
gen1Step spec m refdyn pdb set strategy = do
    let Ops{..} = constructOps m
        DB{_sections=SectionInfo{..}, ..} = pdb
    let ?spec = spec
        ?m    = m
        ?db   = pdb
        ?rd   = refdyn
    tagNopCond <- compileExpr (mkTagVar I.=== (I.EConst $ I.EnumVal mkTagDoNothing))
    -- Use strategy to determine states where $tagnop is a winning action
    stratinset <- set .& strategy
    stepWaitCond0 <- stratinset .& tagNopCond
    deref stratinset
    deref tagNopCond
    stepWaitCond1 <- bexists _labelCube stepWaitCond0
    deref stepWaitCond0
    stepWaitCond <- bexists _untrackedCube stepWaitCond1
    deref stepWaitCond1
    -- Remove these states from set
    set' <- set .& bnot stepWaitCond
    -- Iterate through what remains
    stepBranches <- mkBranches strategy set'
    return Step{..}

-- consumes input reference
mkBranches :: (?spec::Spec, ?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> DDNode s u -> ST s (Branch s u)
mkBranches strategy set = do
    let ops@Ops{..} = constructOps ?m
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
        RefineDynamic{..} = ?rd
        sd = SynthData sinfo trans (error "mkBranches: combinedTrel is undefined") (error "mkBranches: cont is undefined")
    mcond <- ifCondition ops sd strategy set
    case mcond of
         Nothing   -> do deref set
                         return $ BranchStuck 
         Just cond -> do set'     <- set .& bnot cond
                         Just act <- pickLabel ops sd strategy set'
                         deref set
                         if set' == bfalse
                            then do deref set'
                                    return $ BranchAction cond act
                            else do branch' <- mkBranches strategy set'
                                    return $ BranchITE cond act branch'
