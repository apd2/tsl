{-# LANGUAGE RecordWildCards #-}

module CFASpec(Spec(..),
               Task(..),
               Process(..),
               specTmpVars,
               specGetProcess,
               specAllProcs,
               specGetCFA,
               specInlineWireAlways) where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G


import Util
import CFA
import IVar
import IType
import Inline

data Spec = Spec {
    specEnum   :: [Enumeration],
    specVar    :: [Var],
    specWire   :: CFA,         -- wire assignment
    specAlways :: CFA,         -- always blocks
    specProc   :: [Process],   -- processes
    specCTask  :: [Task]       -- controllable tasks
}

data Task = Task {
    taskName :: String,
    taskCFA  :: CFA
}

data Process = Process {
    procName     :: String,
    procCFA      :: CFA,
    procChildren :: [Process],
    procTask     :: [Task]
}

specTmpVars :: Spec -> [Var]
specTmpVars Spec{..} = filter ((== VarTmp) . varCat) specVar

specGetProcess :: Spec -> PID -> Process
specGetProcess spec (name:names) | names == [] = root
                                 | otherwise   = specGetProcess' root names
    where root = fromJustMsg "specGetProcess: error" $ find ((== name) . procName) $ specProc spec

specGetProcess' :: Process -> PID -> Process
specGetProcess' proc (name:names) | names == [] = child
                                  | otherwise   = specGetProcess' child names
    where child = fromJustMsg "specGetProcess': error" $ find ((== name) . procName) $ procChildren proc

specGetCFA :: Spec -> PID -> Maybe String -> CFA
specGetCFA spec [] (Just meth)  = taskCFA $ fromJustMsg "specGetCFA: error1" $ find ((==meth) . taskName) $ specCTask spec
specGetCFA spec pid Nothing     = procCFA $ specGetProcess spec pid
specGetCFA spec pid (Just meth) = taskCFA task
    where proc = specGetProcess spec pid
          task = fromJustMsg "specGetCFA: error2" $ find ((== meth) . taskName) $ procTask proc

specAllProcs :: Spec -> [(PID, CFA)]
specAllProcs Spec{..} = concatMap (\p -> procAllProcs [] p) specProc ++
                        map (\Task{..} -> ([taskName], taskCFA)) specCTask

procAllProcs :: PID -> Process -> [(PID, CFA)]
procAllProcs parpid Process{..} = (pid, procCFA) :
                                  concatMap (procAllProcs pid) procChildren ++
                                  map (\Task{..} -> (parpid++[taskName], taskCFA)) procTask
    where pid = parpid ++ [procName]

specInlineWireAlways :: Spec -> Spec
specInlineWireAlways spec = 
    spec { specProc  = map (procInlineWireAlways spec) $ specProc spec
         , specCTask = map (taskInlineWireAlways spec) $ specCTask spec
         }

procInlineWireAlways :: Spec -> Process -> Process
procInlineWireAlways spec proc = 
    proc { procCFA      = cfaInlineWireAlways spec $ procCFA proc
         , procChildren = map (procInlineWireAlways spec) $ procChildren proc
         , procTask     = map (taskInlineWireAlways spec) $ procTask proc
         }

taskInlineWireAlways :: Spec -> Task -> Task
taskInlineWireAlways spec task = 
    task { taskCFA = cfaInlineWireAlways spec $ taskCFA task}

cfaInlineWireAlways :: Spec -> CFA -> CFA
cfaInlineWireAlways spec cfa = foldl' (\cfa loc -> let cfa' = inlineLoc cfa loc (specAlways spec)
                                                   in inlineLoc cfa' loc (specWire spec)) 
                                      cfa locs
    -- Find delay locations with outgoing transitions
    where locs = filter (\loc -> (isDelayLabel $ cfaLocLabel loc cfa) && (G.suc cfa loc /= []))
                        $ G.nodes cfa

inlineLoc :: CFA -> Loc -> CFA -> CFA
inlineLoc cfa loc inscfa = inlineBetween cfa loc loc' inscfa
    -- Replicate location.  The new location is not a delay location
    -- and contains all outgoing transitions of the original location
    where (cfa1, loc') = cfaInsLoc (LInst ActNone) cfa
          cfa2 = foldl' (\cfa (toloc, lab) -> G.delLEdge (loc, toloc, lab) 
                                              $ cfaInsTrans loc' toloc lab cfa)
                        cfa1 (G.lsuc cfa loc)

inlineBetween :: CFA -> Loc -> Loc -> CFA -> CFA
inlineBetween cfa bef aft inscfa = 
    let -- for each node in inscfa, create a replica in CFA and store
        -- correspondence in a table
        (cfa1, locs) = foldl' (\(cfa,locs) loc -> let lab = cfaLocLabel loc inscfa
                                                      (cfa', loc') = cfaInsLoc lab cfa
                                                  in if' (loc == cfaInitLoc)                       (cfa, locs ++ [bef]) $
                                                     if' (loc == cfaErrLoc)                        (cfa, locs ++ [loc]) $
                                                     if' (isDelayLabel $ cfaLocLabel loc inscfa) (cfa, locs ++ [aft]) $
                                                     (cfa', locs++[loc']))
                              (cfa,[]) (G.nodes inscfa)
        match = M.fromList $ zip (G.nodes inscfa) locs
    in -- copy transitions over
       foldl' (\cfa (from, to, l) -> cfaInsTrans (match M.! from) (match M.! to) l cfa) cfa1 (G.labEdges inscfa)
