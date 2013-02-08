module CFASpec(Spec(..),
               Task(..),
               Process(..),
               specGetProcess,
               specGetCFA,
               specInlineWireAlways) where

import qualified Data.Graph.Inductive.Graph as Graph

import CFA
import IVar
import IType

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
    taskCFA  :: (CFA, [Var])
}

data Process = Process {
    procName     :: String,
    procCFA      :: (CFA, [Var]),
    procChildren :: [Process],
    procTask     :: [Task]
}

specGetProcess :: Spec -> PID -> Process
specGetProcess (name:names) | names == [] = root
                            | otherwise   = specGetProcess' root names
    where root = fromJustMsg "specGetProcess: error" $ find ((== name) . procName) $ specProc spec

specGetProcess' :: Process -> PID -> Process
specGetProcess' proc (name:names) | names == [] = child
                                  | otherwise   = specGerProcess' child names
    where child = fromJustMsg "specGetProcess': error" $ find ((== name) . procName) $ procChildren proc

specGetCFA :: Spec -> PID -> Maybe String -> CFA
specGetCFA spec [] (Just meth)  = fst $ taskCFA $ fromJust "specGetCFA: error1" $ find ((==meth) . taskName) $ specCTask spec
specGetCFA spec pid Nothing     = fst $ procCFA $ specGetProcess spec pid
specGetCFA spec pid (Just meth) = fst $ taskCFA task
    where proc = specGetProcess spec pid
          task = fromJustMsg "specGetCFA: error2" $ find ((== meth) . taskName) $ procTask proc

specInlineWireAlways :: Spec -> Spec
specInlineWireAlways spec = 
    spec { specProc  = map (procInlineWireAlways spec) $ specProc spec
         , specCTask = map (taskInlineWireAlways spec) $ specTask spec
         }

procInlineWireAlways :: Spec -> Process -> Process
procInlineWireAlways spec proc = 
    proc { procCFA      = mapFst (cfaInlineWireAlways spec) $ procCFA proc
         , procChildren = map (procInlineWireAlways spec) $ procChildren proc
         , procTask     = map (taskInlineWireAlways spec) $ procTask proc
         }

taskInlineWireAlways :: Spec -> Task -> Task
taskInlineWireAlways spec task = 
    task { taskCFA = mapFst (cfaInlineWireAlways spec) $ taskCFA task}

cfaInlineWireAlways :: Spec -> CFA -> CFA
cfaInlineWireAlways spec cfa = foldl' (\cfa loc -> let cfa' = inlineLoc cfa loc (specAlways spec)
                                                   in inlineCFA cfa' loc (specWire spec)) 
                                      cfa locs
    -- Find delay locations with outgoing transitions
    where locs = filter (\loc -> (I.isDelayLabel $ I.cfaLocLabel loc cfa) && (G.suc cfa loc /= []))
                        $ G.nodes cfa

inlineLoc :: I.CFA -> I.Loc -> I.CFA -> I.CFA
inlineLoc cfa loc inscfa = inlineBetween spec cfa loc loc' inscfa
    -- Replicate location.  The new location is not a delay location
    -- and contains all outgoing transitions of the original location
    where (cfa1, loc') = I.cfaInsLoc (I.LInst I.ActNone) cfa
          cfa2 = foldl' (\cfa (toloc, lab) -> G.delLEdge (loc, toloc, lab) 
                                              $ I.cfaInsTrans loc' toloc lab cfa)
                        cfa1 (G.lsuc cfa loc)

inlineBetween :: I.CFA -> I.Loc -> I.Loc -> I.CFA -> I.CFA
inlineBetween cfa bef aft inscfa = 
    let -- for each node in inscfa, create a replica in CFA and store
        -- correspondence in the tabl
        (cfa1, locs) = foldl' (\cfa locs -> if' (loc == I.cfaInitLoc)                       (cfa, locs ++ [bef]) $
                                            if' (loc == I.cfaErrLoc)                        (cfa, locs ++ [loc]) $
                                            if' (I.isDelayLabel $ I.cfaLocLabel loc inscfa) (cfa, locs ++ [aft]) $
                                            ((cfa', locs++[loc'])
                                             where lab = I.cfaLocLabel loc inscfa
                                                   (cfa', loc') = I.cfaInsLoc lab cfa))
                              cfa (G.nodes inscfa)
        match = M.fromList $ zip (G.nodes inscfa) locs
    in -- copy transitions over
       foldl' (\cfa (from, to, l) -> I.cfaInsTrans (match M.! from) (match M.! to) cfa l) cfa1 (G.labEdges inscfa)
