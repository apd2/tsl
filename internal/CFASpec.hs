module CFASpec(Spec(..),
               Task(..),
               Process(..)) where

import CFA
import IVar

data Spec = Spec {
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
