module Internal.IRelation(Relation(..),
                 Apply(..),
                 Rule(..)) where

import Internal.IType
import Internal.IExpr
import Ops

data Rule = Rule { ruleOp   :: LogicOp
                 , ruleExpr :: Expr
                 }

data Relation = Relation { relName  :: String
                         , relArgs  :: [(String, Type)]
                         , relRules :: [Rule]
                         }

data Apply = Apply { applyRel  :: String
                   , applyArgs :: [Expr]
                   }
