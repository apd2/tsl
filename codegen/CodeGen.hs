
-- Annotate pause locations with sets of states
-- Assumes that pause locations that represent magic blocks do not have outgoing transitions.
cfaAnnotateReachable :: CFA -> DDNode -> M.Map Loc DDNode
cfaAnnotateReachable =
    where 
    -- decompose into transitions
    states = I.cfaDelayLocs cfa
    tcfas = concatMap (cfaLocTrans cfa) states
    trans = map (\tcfa -> let from = head $ I.cfaSource tcfa
                              to   = head $ I.cfaSink tcfa
                          in I.Transition from to tcfa) tcfas

    -- compile transitions
    -- fix point computation


compileTransition :: Transition -> DDNode


-- Enumerate MBs in the spec.
-- Compile action - refreshes all magic blocks.
-- coords-to-magic block mapping
-- magic block-to-state set mapping
-- state-set to statement mapping (Adam)
-- concretise statement
-- abstract statement
-- simulate abstract statement
-- Generate action 
