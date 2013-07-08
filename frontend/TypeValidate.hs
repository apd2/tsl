{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module TypeValidate (validateTypeSpec,
                     validateTypeSpec2,
                     validateTypeDeps) where

import Control.Monad.Error
import Data.List

import TSLUtil
import Pos
import NS
import Spec
import Type
import TypeOps
import {-# SOURCE #-} ExprOps
import ExprValidate


---------------------------------------------------------------------
-- Validate individual TypeSpec
---------------------------------------------------------------------

validateTypeSpec :: (?spec::Spec, MonadError String me) => Scope -> TypeSpec -> me ()

-- * Struct fields must have unique names and valid types
validateTypeSpec sc (StructSpec _ fs) = do
    uniqNames (\n -> "Field " ++ n ++ " declared multiple times ") fs
    _ <- mapM (validateTypeSpec sc . tspec) fs
    return ()

validateTypeSpec sc (ArraySpec _ t _) = validateTypeSpec sc t
validateTypeSpec sc (PtrSpec _ t)     = validateTypeSpec sc t


-- * user-defined type names refer to valid types
validateTypeSpec sc (UserTypeSpec _ n) = do {checkTypeDecl sc n; return ()}

validateTypeSpec _  _ = return ()


-- Second pass: validate array sizes
validateTypeSpec2 :: (?spec::Spec, MonadError String me) => Scope -> TypeSpec -> me ()
validateTypeSpec2 s (ArraySpec _ t l) = do
    let ?scope = s
        ?privoverride = False
    validateExpr' l
    assert (isConstExpr l) (pos l)  $ "Array length must be a constant expression"
    assert (isInt l) (pos l)        $ "Array length must be an integer expression"
    assert (evalInt l >= 0) (pos l) $ "Array length must be non-negative"
    validateTypeSpec2 s t

validateTypeSpec2 s (StructSpec _ fs) = do
    _ <- mapM (validateTypeSpec2 s . tspec) fs
    return ()

validateTypeSpec2 s (PtrSpec _ t) = validateTypeSpec2 s t

validateTypeSpec2 _ _ = return ()


---------------------------------------------------------------------
-- Check that the graph of dependencies among TypeDecl's is acyclic
---------------------------------------------------------------------


validateTypeDeps :: (?spec::Spec, MonadError String me) => me ()
validateTypeDeps = 
    case grCycle tdeclGraph of
         Nothing -> return ()
         Just c  -> err (pos $ snd $ head c) $ "Cyclic type aggregation: " ++ (intercalate "->" $ map (show . snd) c)
