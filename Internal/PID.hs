{-# LANGUAGE ImplicitParams #-}

module Internal.PID (PrID(..),
            EPID(..),
            NSID(..),
            pidIdle,
            parsePID,
            childPID,
            epid2nsid) where

import Text.PrettyPrint
import Data.List.Split

import Util
import PP
import Frontend.NS
import Frontend.Method

-- Process ID: root process or forked process

data PrID = PrID String [String] 
            deriving Eq

instance PP PrID where
    pp (PrID p ps) = hcat $ punctuate (char '/') (map text $ p:ps)

instance Show PrID where
    show = render . pp

pidIdle = PrID "_idle_" []

parsePID :: String -> PrID
parsePID s = PrID (head toks) (tail toks) where toks = splitOn "/" s


childPID :: PrID -> String -> PrID
childPID (PrID p ps) pname = PrID p (ps ++ [pname])

-- Extended PID: process id or controllable transition
data EPID = EPIDProc  PrID
          | EPIDCont

instance Eq EPID where
    (==) (EPIDProc p1)  (EPIDProc p2)  = p1 == p2
    (==) EPIDCont       EPIDCont       = True
    (==) _              _              = False

instance PP EPID where
    pp (EPIDProc  pid) = pp pid
    pp EPIDCont        = text "$contproc"

instance Show EPID where
    show = render . pp

--parseEPID :: String -> EPID
--parseEPID s = if' (s=="$contproc") EPIDCont (EPIDProc $ parsePID s)

epid2nsid :: EPID -> Scope -> NSID
epid2nsid epid sc = NSID mpid mmeth
    where
    mpid = case epid of
                EPIDProc pid -> Just pid
                _            -> Nothing
    mmeth = case sc of
                 ScopeMethod _ m -> Just m
                 _               -> Nothing

-- Namespace ID: 
-- Just/Just       = method executing within a process
-- Just/Nothing    = process namespace
-- Nothing/Just    = method executing outside a process scope
-- Nothing/Nothing = top-level scope
data NSID = NSID (Maybe PrID) (Maybe Method)

--instance PP NSID where
--    pp (NSID mpid ms) = hcat $ punctuate (char '/')
--                        $ fromMaybe [] (\(PrID p ps) -> p:ps) mpid ++ fromMaybe [] (\s -> [s++"()"]) ms
--    
--instance Show NSID where
--    show = pp . render



--procNameIdle = "$pididle"
--
--pidIdle = [procNameIdle]
