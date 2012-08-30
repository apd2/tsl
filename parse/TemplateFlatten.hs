{-# LANGUAGE ImplicitParams #-}

module TemplateFlatten(tmMergeParents) where

import Pos
import Name
import Spec
import Template
import TemplateOps

-- Merge template with its parents
-- Assumes that constants and enums have already been flattened
tmMergeParents :: (?spec::Spec) => Template -> Template
tmMergeParents tm = Template (pos tm)
                             (name tm)
                             (tmPort tm)
                             []                    -- tmDerive
                             []                    -- tmConst
                             []                    -- tmTypeDecl
                             (tmAllVar tm)
                             (tmAllWire tm)
                             (tmAllInst tm)
                             (tmAllInit tm)
                             (tmAllProcess tm)
                             (tmAllMethod tm)
                             (tmAllGoal tm)
