{-# LANGUAGE ImplicitParams #-}

module PID (PrID(..),
            EPID(..),
            CID(..),
            NSID(..),
            parseEPID,
            pid2cid,
            childPID,
            cid2nsid,
            cid2epid,
            cid2mpid,
            epid2nsid) where

import Text.PrettyPrint
import Data.List.Split

import Util
import Pos
import PP
import NS
import Name
import Method
import Spec
import Expr

-- Process ID: root process or forked process

data PrID = PrID String [String] 
            deriving Eq

instance PP PrID where
    pp (PrID p ps) = hcat $ punctuate (char '/') (map text $ p:ps)

instance Show PrID where
    show = render . pp

childPID :: PrID -> String -> PrID
childPID (PrID p ps) pname = PrID p (ps ++ [pname])

pid2cid :: PrID -> CID
pid2cid pid = UCID pid Nothing

-- Extended PID: process id, controllable task process, or controllable transition
data EPID = EPIDProc  PrID
          | EPIDCTask Method
          | EPIDCont

instance Eq EPID where
    (==) (EPIDProc p1)  (EPIDProc p2)  = p1 == p2
    (==) (EPIDCTask m1) (EPIDCTask m2) = sname m1 == sname m2
    (==) EPIDCont       EPIDCont       = True
    (==) _              _              = False

instance PP EPID where
    pp (EPIDProc  pid) = pp pid
    pp (EPIDCTask m)   = (text $ sname m) <> text "()"
    pp EPIDCont        = text "$contproc"

instance Show EPID where
    show = render . pp

parseEPID :: Spec -> String -> EPID
parseEPID spec s = if' (s=="$contproc")                         EPIDCont                            $
                   if' ((take 2 $ reverse $ last toks) == ")(") (EPIDCTask $ methodByName $ init $ init $ last toks) $
                   (EPIDProc $ PrID (head toks) (tail toks))
                   where toks = splitOn "/" s
                         methodByName n = let ?spec = spec 
                                          in snd $ getMethod (ScopeTemplate $ head $ specTemplate ?spec) (MethodRef nopos [Ident nopos n])

epid2nsid :: EPID -> Scope -> NSID
epid2nsid epid sc = NSID mpid mmeth
    where
    mpid = case epid of
                EPIDProc pid -> Just pid
                _            -> Nothing
    mmeth = case sc of
                 ScopeMethod _ m -> Just m
                 _               -> Nothing

-- CFA ID: process, controllable, or uncontrollable task, or controllable transition
data CID = UCID  PrID (Maybe Method)
         | CTCID Method
         | CCID

instance Eq CID where
    (==) (UCID p1 Nothing)   (UCID p2 Nothing)   = p1 == p2 
    (==) (UCID p1 (Just m1)) (UCID p2 (Just m2)) = p1 == p2 && sname m1 == sname m2
    (==) (CTCID m1)          (CTCID m2)          = sname m1 == sname m2
    (==) CCID                CCID                = True
    (==) _                   _                   = False

instance PP CID where
    pp (UCID pid mm) = pp pid <> case mm of 
                                      Nothing -> empty
                                      Just m  -> char '/' <> (text $ sname m) <> text "()"
    pp (CTCID m)     = (text $ sname m) <> text "()"
    pp CCID          = text "$contcfa"

instance Show CID where
    show = render . pp

instance Read CID where
    readsPrec = error "Read CID not implemented"

cid2epid :: CID -> EPID
cid2epid (UCID pid _) = EPIDProc pid
cid2epid (CTCID m)    = EPIDCTask m
cid2epid CCID         = EPIDCont

cid2nsid :: CID -> NSID
cid2nsid (UCID pid mm) = NSID (Just pid) mm
cid2nsid (CTCID m)     = NSID Nothing    (Just m)
cid2nsid CCID          = NSID Nothing    Nothing

cid2mpid :: CID -> Maybe PrID
cid2mpid (UCID pid _) = Just pid
cid2mpid _            = Nothing

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
