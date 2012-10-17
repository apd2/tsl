{-# LANGUAGE ImplicitParams #-}

module ISpec(Goal(..),
             Transition(..),
             Spec(..),
             getVar,
             getEnum) where

import Data.List
import Data.Maybe
import qualified Data.Map as M

import Util hiding (name)
import TSLUtil
import Common
import IType
import IExpr
import IVar
import CFA

data Transition = Transition { tranFrom :: Loc
                             , tranTo   :: Loc
                             , tranCFA  :: CFA
                             }

data Goal = Goal { goalName :: String
                 , goalCond :: Transition
                 }

data Spec = Spec { specEnum  :: [Enumeration]
                 , specVar   :: [Var]
                 , specCTran :: [Transition]
                 , specUTran :: [Transition]
                 , specWire  :: Transition
                 , specInit  :: (Transition, Expr) -- initial state constraint (constraint_on_spec_variables,constraints_on_aux_variables)
                 , specGoal  :: [Goal] 
                 , specFair  :: [Expr]             -- sets of states f s.t. GF(-f)
                 }

getVar :: (?spec::Spec) => String -> Var
getVar n = fromJustMsg ("getVar: variable " ++ n ++ " not found") 
                       $ find ((==n) . varName) $ specVar ?spec 

getEnum :: (?spec::Spec) => String -> Enumeration
getEnum e = fromJustMsg ("getEnum: enumerator " ++ e ++ " not found")
                        $ find (elem e . enumEnums) $ specEnum ?spec
