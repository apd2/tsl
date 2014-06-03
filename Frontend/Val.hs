module Frontend.Val(Val(..),
           TVal(TVal),
           WithVal(..)) where

import qualified Data.Map as M

import Name
import Frontend.NS
import Frontend.Expr
import Frontend.Type

-- Value
data Val = BoolVal          Bool
         | IntVal           Integer
         | StructVal        (M.Map Ident TVal)
         | EnumVal          Ident
         | PtrVal           LExpr
--         | ArrayVal         [TVal]
         | NondetVal

class WithVal a where
    val :: a -> Val

data TVal = TVal {ttyp::Type, tval::Val}

instance WithType TVal where
    typ = ttyp

instance WithVal TVal where
    val = tval

-- Assumed comparable types
instance Eq Val where
    (==) (BoolVal b1)   (BoolVal b2)   = b1 == b2
    (==) (IntVal i1)    (IntVal i2)    = i1 == i2
    (==) (StructVal s1) (StructVal s2) = and $ map (uncurry (==)) (zip (map snd $ M.toList s1) (map snd $ M.toList s2))
    (==) (PtrVal p1)    (PtrVal p2)    = error $ "Eq PtrVal not implemented"
--    (==) (ArrayVal a1)  (ArrayVal a2)  = and $ map (uncurry (==)) (zip a1 a2)
    (==) _              _              = False

instance Eq TVal where
    (==) (TVal t1 v1) (TVal t2 v2)     = v1 == v2

instance Ord Val where
    compare (IntVal i1) (IntVal i2)   = compare i1 i2
    compare _           _             = error "Incomparable values in Ord Val"

instance Ord TVal where
    compare (TVal t1 v1) (TVal t2 v2) = compare v1 v2
