{-# LANGUAGE ImplicitParams #-}

-- Instance tree used in flattening the specification

module InstTree (IID,
                 mapInstTree,
                 itreeTemplate,
                 itreeFlattenName,
                 itreeParseName,
                 itreeRelToAbsPath,
                 itreeAbsToRelPath) where

import qualified Data.Tree as T
import Data.List
import Data.String.Utils

import Util hiding (name)
import Name
import Pos
import Spec
import Template
import NS

-- Instance descriptor (path in the instance tree)
type IID = [Ident]

-- Instance tree root
itreeRoot :: (?spec::Spec) => Template
itreeRoot = fromJustMsg ("fromJustMsg itreeRoot") $ find ((== "main") . sname) (specTemplate ?spec)

-- Template from instance descriptor
itreeTemplate :: (?spec::Spec) => IID -> Template
itreeTemplate ns = itreeTemplate' itreeRoot ns

itreeTemplate' :: (?spec::Spec) => Template -> [Ident] -> Template
itreeTemplate' tm []     = tm
itreeTemplate' tm (n:ns) = itreeTemplate' (getTemplate $ instTemplate $ fromJustMsg ("fromJustMsg itreeTemplate'") $ find ((==n) . name) (tmInst tm)) ns

-- Map function over all templates in the instance tree;
-- return list of resulting values
mapInstTree :: (?spec::Spec) => (IID -> Template -> a) -> [a]
mapInstTree f = mapInstTree' f []

mapInstTree' :: (?spec::Spec) => (IID -> Template -> a) -> IID -> [a]
mapInstTree' f iid = (f iid (itreeTemplate iid)):
                     concatMap (\i -> mapInstTree' f (iid++[name i])) (tmInst $ itreeTemplate iid)

itreeFlattenName :: IID -> Ident -> Ident
itreeFlattenName iid i = Ident (pos i) $ intercalate ":" $ map sname (iid ++ [i])

itreeParseName :: Ident -> (IID, Ident)
itreeParseName i = (map atNopos $ init ids, atNopos $ last ids)
    where ids = split ":" (sname i)
          atNopos x = Ident nopos x
          

-- Translate relative path in the instance tree to absolute path
-- iid  - path to a template in the tree
-- path - relative path (through port and instance names) from this
--        template to another template in the tree
-- returns absolute path to the template referenced by the path
itreeRelToAbsPath :: (?spec::Spec) => IID -> [Ident] -> IID
itreeRelToAbsPath iid path = foldl' itreeRelToAbsPath' iid path

itreeRelToAbsPath' :: (?spec::Spec) => IID -> Ident -> IID
itreeRelToAbsPath' iid n = 
    case objGet (ObjTemplate $ itreeTemplate iid) n of
         ObjInstance _ i -> iid ++ [n]
         ObjPort _ p     -> itreeRelToAbsPath' (init iid) portVal
    where portIdx = fromJustMsg "fromJustMsg itreeRelToAbsPath'" $ findIndex ((== n) . name) (tmPort $ itreeTemplate iid)
          parent = itreeTemplate $ init iid
          parentInst = fromJustMsg "fromJustMsg itreeRelToAbsPath.parentInst'" $ find ((== last iid) . name) $ tmInst parent
          portVal = (instPort parentInst) !! portIdx


-- Given two instances, compute a relative path from the first to the second 
-- instance, if one exists
itreeAbsToRelPath :: (?spec::Spec) => IID -> IID -> Maybe [Ident]
itreeAbsToRelPath from to = error "itreeAbsToRelPath not implemented"
