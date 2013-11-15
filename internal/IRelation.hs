module IRelation(Relation(..),
                 Apply(..)) where

import IType
import IExpr
import CFA

data Relation = Relation { relName  :: String
                         , relArgs  :: [(String, Type)]
                         , relRules :: [CFA]
                         }

data Apply = Apply { applyRel  :: String
                   , applyArgs :: [Expr]
                   }
