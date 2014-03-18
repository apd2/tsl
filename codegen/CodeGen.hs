{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module CodeGen (Step(..),
                Branch(..),
                gen1Step,
                derefStep) where

import Data.Tuple.Select
import qualified Data.Map          as M
import Control.Monad
import Control.Applicative
import Data.Maybe
import Data.List

import TSLUtil
import Util
import Interface
import TermiteGame
import BddRecord
import Predicate
import AbsSim
import ISpec hiding (getVar)
import Inline
import CG
import BFormula
import qualified IExpr             as I
import qualified CuddExplicitDeref as C
import qualified BddUtil           as C
import qualified DbgTypes          as D

data Branch s u = BranchITE    (DDNode s u) (DDNode s u) (Branch s u)
                | BranchAction (DDNode s u) (DDNode s u)
                | BranchStuck  

-- A single synthesised step, consisting of a wait condition and
-- an if-then-else fork.
data Step s u = Step { stepWaitCond :: DDNode s u -- wait condition
                     , stepBranches :: Branch s u 
                     }

derefStep :: C.STDdManager s u -> Step s u -> ST s ()
derefStep m (Step cond branch) = do
    C.deref m cond
    derefBranch m branch

derefBranch :: C.STDdManager s u -> Branch s u -> ST s ()
derefBranch m (BranchITE i t e) = do
    C.deref m i
    C.deref m t
    derefBranch m e
derefBranch m (BranchAction i t) = do
    C.deref m i
    C.deref m t
derefBranch m BranchStuck = return ()

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
         Just cond -> do condset  <- set .& cond
                         deref set
                         Just act <- pickLabel ops sd strategy condset
                         deref condset
                         set'     <- set .& bnot cond
                         if set' == bfalse
                            then do deref set'
                                    return $ BranchAction cond act
                            else do branch' <- mkBranches strategy set'
                                    return $ BranchITE cond act branch'

-- Decomposes cond into prime implicants and converts it to a boolean expression
mkCondition :: Spec -> C.STDdManager s u -> DB s u AbsVar AbsVar -> DDNode s u -> ST s I.Expr
mkCondition spec m pdb cond = do
    let ?spec = spec
    let ops@Ops{..} = constructOps m
    cubes <- C.primeCover ops cond
    res <- I.disj <$> mapM (mkCondCube m pdb) cubes
    mapM_ deref cubes
    return res

mkCondCube :: (?spec::Spec) => C.STDdManager s u -> DB s u AbsVar AbsVar -> DDNode s u -> ST s I.Expr
mkCondCube m DB{_symbolTable = SymbolInfo{..}, ..} cub = do
   let ops@Ops{..} = constructOps m
   asns <- cubeToAsns ops cub $ map (mapSnd sel2) $ M.toList _stateVars 
   return $ I.conj 
          $ map (\(av, vals) -> I.disj $ map (formToExpr . avarAsnToFormula av) vals) asns
    

cubeToAsns :: Ops s u -> DDNode s u -> [(AbsVar, [Int])] -> ST s [(AbsVar, [Integer])]
cubeToAsns Ops{..} rel vs = do
    support <- supportIndices rel
    asn     <- satCube rel
    let supvars = filter (any (\idx -> elem idx support) . snd) vs
    return $ map (\(av, is) -> (av, map boolArrToBitsBe $ (<$*>) $ map (C.expand . (asn !!)) is))
           $ nub supvars
