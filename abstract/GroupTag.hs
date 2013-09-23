module GroupTag(avarGroupTag) where 

import Predicate
import Inline

avarGroupTag :: AbsVar -> Maybe String
--avarGroupTag (AVarBool t)                               | (isFairVarName $ show t)          = Just "$fair"
--avarGroupTag (AVarPred (PAtom _ (PTInt t1) (PTInt t2))) | isSimpleTerm t1 && isConstTerm t2 = fmap show $ simpleTermAtom t1
--avarGroupTag (AVarPred (PAtom _ (PTInt t1) (PTInt t2))) | isConstTerm t1 && isSimpleTerm t2 = fmap show $ simpleTermAtom t2
avarGroupTag _                                                                              = Nothing

-- A simple term depends on at most one scalar variable
-- x[const]  - yes
-- x[y]      - no
-- x + const - yes
-- x+y       - no

isSimpleTerm :: Term -> Bool
isSimpleTerm (TVar _)         = True
isSimpleTerm (TSInt _ _)      = True
isSimpleTerm (TUInt _ _)      = True
isSimpleTerm (TEnum _)        = True
isSimpleTerm TTrue            = True
isSimpleTerm (TAddr t)        = isSimpleTerm t
isSimpleTerm (TField t _)     = isSimpleTerm t
isSimpleTerm (TIndex t i)     = isSimpleTerm t && isConstTerm i
isSimpleTerm (TUnOp _ t)      = isSimpleTerm t
isSimpleTerm (TBinOp _ t1 t2) = (isSimpleTerm t1 && isConstTerm t1) || (isConstTerm t1 && isSimpleTerm t2)
isSimpleTerm (TSlice t _)     = isSimpleTerm t

simpleTermAtom :: Term -> Maybe Term
simpleTermAtom t@(TVar _)         = Just t
simpleTermAtom   (TSInt _ _)      = Nothing
simpleTermAtom   (TUInt _ _)      = Nothing
simpleTermAtom   (TEnum _)        = Nothing
simpleTermAtom   TTrue            = Nothing
simpleTermAtom   (TAddr _)        = Nothing
simpleTermAtom t@(TField _ _)     = Just t
simpleTermAtom t@(TIndex _ _)     = Just t
simpleTermAtom   (TUnOp _ t)      = Just t
simpleTermAtom   (TBinOp _ t1 t2) | isConstTerm t1 = simpleTermAtom t2
                                  | isConstTerm t2 = simpleTermAtom t1
simpleTermAtom   (TSlice t _)     = simpleTermAtom t

