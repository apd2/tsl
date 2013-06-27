{-# LANGUAGE RecordWildCards, ImplicitParams #-}

module ISpec(Spec(..),
             Task(..),
             Process(..),
             specTmpVar,
             specStateVar,
             specGetProcess,
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
import CFA
import IVar
import IType
import Inline
import TranSpec
import PP

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

specAllCFAs :: Spec -> [(PID, CFA)]
specAllCFAs Spec{..} = concatMap (\p -> procAllCFAs [] p) specProc ++
                       map (\Task{..} -> ([taskName], taskCFA)) specCTask

procAllCFAs :: PID -> Process -> [(PID, CFA)]
procAllCFAs parpid Process{..} = (pid, procCFA) :
                                 concatMap (procAllCFAs pid) procChildren ++
                                 map (\Task{..} -> (pid++[taskName], taskCFA)) procTask
    where pid = parpid ++ [procName]

specAllProcs :: Spec -> [(PID, Process)]
specAllProcs Spec{..} = concatMap (     procAllForkedProcs []) specProc

procAllForkedProcs :: PID -> Process -> [(PID, Process)]
procAllForkedProcs parpid p@Process{..} = (pid, p) : concatMap (procAllForkedProcs pid) procChildren
    where pid = parpid ++ [procName]

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
