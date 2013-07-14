{-# LANGUAGE RecordWildCards, ImplicitParams #-}

module ISpec(Spec(..),
             Task(..),
             taskName,
             Process(..),
             specTmpVar,
             specStateVar,
             specGetProcess,
             specGetCTask,
             specAllCFAs,
             specAllProcs,
             specGetCFA,
             specMapCFA,
             specInlineWireAlways,
             cfaLocInlineWireAlways,
             lookupVar,
             getVar,
             lookupEnumerator,
             getEnumerator,
             getEnumeration,
             enumToInt) where

import Data.List
import Data.Maybe
import qualified Data.Graph.Inductive.Graph as G
import Text.PrettyPrint

import Util
import Name
import CFA
import IVar
import IType
import TranSpec
import PP
import PID
import qualified Method as F

data Task = Task {
    taskMethod :: F.Method,
    taskCFA    :: CFA
}

taskName :: Task -> String
taskName = sname . taskMethod

data Process = Process {
    procName     :: String,
    procCFA      :: CFA,
    procChildren :: [Process],
    procTask     :: [Task]
}

data Spec = Spec {
    specEnum   :: [Enumeration],
    specVar    :: [Var],
    specWire   :: Maybe CFA,   -- wire assignment
    specAlways :: Maybe CFA,   -- always blocks
    specProc   :: [Process],   -- processes
    specCTask  :: [Task],      -- controllable tasks
    specCAct   :: CFA,         -- controllable transitions
    specTran   :: TranSpec     -- info required for variable update
                               -- computation
}

specStateVar :: Spec -> [Var]
specStateVar = filter ((==VarState) . varCat) . specVar

specTmpVar :: Spec -> [Var]
specTmpVar = filter ((==VarTmp) . varCat) . specVar

instance PP Spec where
    pp Spec{..} = (vcat $ map (($+$ text "") . pp) specEnum)
                  $+$
                  (vcat $ map (($+$ text "") . pp) specVar)
                  $+$
                  pp specTran 

lookupVar :: (?spec::Spec) => String -> Maybe Var
lookupVar n = find ((==n) . varName) $ specVar ?spec 

getVar :: (?spec::Spec) => String -> Var
getVar n = fromJustMsg ("getVar: variable " ++ n ++ " not found") $ lookupVar n

lookupEnumerator :: (?spec::Spec) => String -> Maybe Enumeration
lookupEnumerator e = find (elem e . enumEnums) $ specEnum ?spec

getEnumerator :: (?spec::Spec) => String -> Enumeration
getEnumerator e = fromJustMsg ("getEnumerator: enumerator " ++ e ++ " not found") $ lookupEnumerator e

getEnumeration :: (?spec::Spec) => String -> Enumeration
getEnumeration e = fromJustMsg ("getEnumeration: enumeration " ++ e ++ " not found")
                   $ find ((==e) . enumName) $ specEnum ?spec

-- Get sequence number of an enumerator
enumToInt :: (?spec::Spec) => String -> Int
enumToInt n = fst $ fromJust $ find ((==n) . snd) $ zip [0..] (enumEnums $ getEnumerator n)

specGetProcess :: Spec -> PrID -> Process
specGetProcess spec (PrID n names) | names == [] = root
                                   | otherwise   = specGetProcess' root names
    where root = fromJustMsg ("specGetProcess " ++ n ++ ": error") $ find ((== n) . procName) $ specProc spec

specGetProcess' :: Process -> [String] -> Process
specGetProcess' proc (n:names) | names == [] = child
                               | otherwise   = specGetProcess' child names
    where child = fromJustMsg "specGetProcess': error" $ find ((== n) . procName) $ procChildren proc

specGetCTask :: Spec -> String -> Task
specGetCTask Spec{..} n = fromJust $ find ((== n) . sname . taskMethod) specCTask

specGetCFA :: Spec -> CID -> CFA
specGetCFA spec (UCID pid Nothing)  = procCFA $ specGetProcess spec pid
specGetCFA spec (UCID pid (Just m)) = taskCFA $ fromJust $ find ((== sname m) . taskName) $ procTask $ specGetProcess spec pid
specGetCFA spec (CTCID m)           = taskCFA $ fromJust $ find ((== sname m) . taskName) $ specCTask spec
specGetCFA spec CCID                = specCAct spec 

specAllCFAs :: Spec -> [(CID, CFA)]
specAllCFAs Spec{..} = concatMap (\p -> procAllCFAs (PrID (procName p) []) p) specProc  ++
                       map       (\Task{..} -> (CTCID taskMethod, taskCFA))   specCTask ++
                       [(CCID, specCAct)]

procAllCFAs :: PrID -> Process -> [(CID, CFA)]
procAllCFAs pid proc = (UCID pid Nothing, procCFA proc) :
                       concatMap (\p -> procAllCFAs (childPID pid (procName p)) p) (procChildren proc) ++
                       map (\Task{..} -> (UCID pid (Just taskMethod), taskCFA))    (procTask proc)

specAllProcs :: Spec -> [(PrID, Process)]
specAllProcs Spec{..} = concatMap (\p -> procAllForkedProcs (PrID (procName p) []) p) specProc

procAllForkedProcs :: PrID -> Process -> [(PrID, Process)]
procAllForkedProcs pid p = (pid,p) : (concatMap (\p' -> procAllForkedProcs (childPID pid (procName p')) p') $ procChildren p)

-- Apply transformation to all task and process CFA's in the spec
specMapCFA :: (CFA -> CFA) -> Spec -> Spec
specMapCFA f spec = 
   spec { specProc  = map (procMapCFA f) $ specProc  spec
        , specCTask = map (taskMapCFA f) $ specCTask spec}

procMapCFA :: (CFA -> CFA) -> Process -> Process
procMapCFA f proc = 
    proc { procCFA      = f $ procCFA proc
         , procChildren = map (procMapCFA f) $ procChildren proc
         , procTask     = map (taskMapCFA f) $ procTask     proc
         }

taskMapCFA :: (CFA -> CFA) -> Task -> Task
taskMapCFA f task = task {taskCFA = f $ taskCFA task}

specInlineWireAlways :: Spec -> Spec
specInlineWireAlways spec = specMapCFA (cfaInlineWireAlways spec) spec

cfaInlineWireAlways :: Spec -> CFA -> CFA
cfaInlineWireAlways spec cfa = foldl' (\cfa0 loc -> let cfa1 = case specAlways spec of
                                                                    Nothing -> cfa0
                                                                    Just a  -> cfaLocInline cfa0 loc a
                                                    in case specWire spec of
                                                            Nothing -> cfa1
                                                            Just w  -> cfaLocInline cfa1 loc w) 
                                      cfa locs
    -- Find delay locations with outgoing transitions
    where locs = filter (\loc -> (isDelayLabel $ cfaLocLabel loc cfa) && (G.suc cfa loc /= []))
                        $ G.nodes cfa

cfaLocInlineWireAlways :: Spec -> CFA -> Loc -> CFA
cfaLocInlineWireAlways spec cfa loc =
    let cfa1 = case specAlways spec of
                    Nothing -> cfa
                    Just a  -> cfaLocInline cfa loc a
               in case specWire spec of
                       Nothing -> cfa1
                       Just w  -> cfaLocInline cfa1 loc w    
