{-# LANGUAGE RecordWildCards, ImplicitParams #-}

module CodeGen.CodeGen(exprToTSL2) where

import Data.List
import Text.PrettyPrint

import PP
import Name
import Frontend.InstTree
import Internal.PID
import Frontend.NS
import Internal.IExpr
import Frontend.Inline
import qualified Frontend.Spec as F

data CGVar = PVar {cgvProc::[(IID, String)]                         , cgvVar::String} -- Process-scope variable
           | MVar {cgvProc::[(IID, String)], cgvMethod::(IID,String), cgvVar::String} -- Method-scope variable (argument or local)
           | GVar {cgvInst::IID                                     , cgvVar::String} -- Template-global variable

type CGExpr = GExpr String


ppCGVar :: (?spec::F.Spec, ?pid::PrID, ?sc::Scope) => CGVar -> Doc
ppCGVar v = case cgVarRelName ?spec ?pid ?sc v of
                 Nothing  -> text $ "/*" ++ cgvVar v ++ "*/"
                 Just str -> text str

cgVarRelName :: F.Spec -> PrID -> Scope -> CGVar -> Maybe String
cgVarRelName spec pid sc cgv =
    case cgv of
         PVar{..} -> Nothing -- cannot access process-scope variables inside magic block
         MVar{..} -> if pid' == cgvProc && m' == cgvMethod -- can only access variables inside local method scope
                        then Just cgvVar
                        else Nothing
         GVar{..} -> fmap (\path -> intercalate "." $ (map sname path) ++ [cgvVar])
                          $ let ?spec = spec in itreeAbsToRelPath (fst m') cgvInst
    where PrID p ps       = pid
          ScopeMethod _ m = sc
          pid'            = map itreeParseName (p:ps)
          m'              = itreeParseName $ sname m
                        

exprToCGExpr :: (?spec::F.Spec, ?pid::PrID, ?sc::Scope) => Expr -> CGExpr
exprToCGExpr (EVar n)          = EVar $ render $ ppCGVar $ varToCGVar n
exprToCGExpr (EConst c)        = EConst c
exprToCGExpr (EField e f)      = EField (exprToCGExpr e) f
exprToCGExpr (EIndex a i)      = EIndex (exprToCGExpr a) (exprToCGExpr i)
exprToCGExpr (ERange e (f, t)) = ERange (exprToCGExpr e) (exprToCGExpr f, exprToCGExpr t)
exprToCGExpr (ELength e)       = ELength (exprToCGExpr e)
exprToCGExpr (EUnOp op e)      = EUnOp op (exprToCGExpr e)
exprToCGExpr (EBinOp op e1 e2) = EBinOp op (exprToCGExpr e1) (exprToCGExpr e2)
exprToCGExpr (ESlice e s)      = ESlice (exprToCGExpr e) s
exprToCGExpr (ERel n es)       = ERel n (map exprToCGExpr es)


varToCGVar :: String -> CGVar
varToCGVar v = 
    case (mpid, mmeth) of
         (Nothing , Nothing) -> let (iid, v') = itreeParseName vname 
                                in  GVar iid v'
         (Just pid, Nothing) -> let PrID p ps = pid
                                in  PVar (map itreeParseName (p:ps)) vname
         (Nothing , Just m)  -> MVar [] (itreeParseName m) vname
         (Just pid, Just m)  -> let PrID p ps = pid       
                                in  MVar (map itreeParseName (p:ps)) (itreeParseName m) vname
    where (mpid, mmeth, vname) = parseVarName v


exprToTSL2 :: F.Spec -> PrID -> Scope -> Expr -> Doc
exprToTSL2 spec pid sc e = 
    let ?spec = spec
        ?pid  = pid
        ?sc   = sc
    in pp $ exprToCGExpr e
