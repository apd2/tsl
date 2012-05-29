-- Parsed TSL spec

{-# LANGUAGE TypeSynonymInstances #-}

module Syntax where

import Data.List
import Data.Char
import Text.Parsec.Pos
import Text.PrettyPrint
import Numeric

ppshift = 4

-- pretty-printing class
class PP a where
    pp :: a -> Doc

instance PP String where
    pp s = text s

instance PP Int where
    pp = int

instance PP Integer where
    pp = integer

instance (PP a) => PP (Maybe a) where
    pp Nothing = empty
    pp (Just x) = pp x

nest' = nest ppshift
braces' x = lbrace $+$ nest' x $+$ rbrace

-- Element of a syntax tree with source position
data AtPos a = AtPos {getVal::a, getPos::(SourcePos,SourcePos)}
instance Functor AtPos where
    fmap f (AtPos x p) = AtPos (f x) p

instance (PP a) => PP (AtPos a) where
    pp (AtPos x p) = pp x

atPos :: SourcePos -> a -> SourcePos -> AtPos a
atPos start x end = AtPos x (start,end)

-- Common types
type Slice = (PConstExpr, PConstExpr)  -- low,high
instance PP Slice where
    pp (l,h) = brackets $ pp l <> colon <> pp h 

data Radix = Rad2 | Rad8 | Rad10 | Rad16
instance PP Radix where
    pp Rad2  = text "'b"
    pp Rad8  = text "'o"
    pp Rad10 = text "'d"
    pp Rad16 = text "'h"

data ArgDir = ArgIn | ArgOut
instance PP ArgDir where
    pp ArgIn  = empty
    pp ArgOut = text "out"

data TaskCat = Contr | Uncontr | Invis
instance PP TaskCat where
    pp Contr   = text "controllable"
    pp Uncontr = text "uncontrollable"
    pp Invis   = text "invisible"

-- TSL identifier
type PString = AtPos String
data Selector = Field PString
              | Index PExpr
instance PP Selector where
    pp (Field s) = char '.' <> pp s
    pp (Index i) = brackets $ pp i
type PSelector = AtPos Selector

data Ident = Ident {root :: PString, path :: [PSelector]}
instance PP Ident where
    pp (Ident r p) = pp r <> (hcat $ map pp p)
type PIdent = AtPos Ident


-- A TSL spec is a list of type, constant, and template declarations
type Spec = [PSpecItem]
instance PP Spec where
    pp items = vcat $ intersperse (text "") (map pp items)

data SpecItem = TypeDecl TypeDef
              | ConstDecl ConstDef
              | TemplateDecl Template
instance PP SpecItem where
    pp (TypeDecl t) = pp t <> semi
    pp (ConstDecl c) = pp c <> semi
    pp (TemplateDecl t) = pp t 
type PSpecItem = AtPos SpecItem

data TypeDef = TypeDef PType PString
instance PP TypeDef where
    pp (TypeDef t n) = text "typedef" <+> pp t <+> pp n

data ConstDef = ConstDef PType PString PConstExpr
instance PP ConstDef where
    pp (ConstDef t n e) = text "const" <+> pp t <+> pp n <+> char '=' <+> pp e

-- Type declaration
data Type = IntType Bool Int                     -- signed/unsigned, width
          | BoolType
          | UserType PString                     -- name of a user-defined type
          | EnumType [(String, Maybe PConstExpr)]
          | StructType [(PType, PString)]
          | ArrayType PType PConstExpr           -- element type, length
instance PP Type where
    pp (IntType True i)  = text "sint" <> char '<' <> pp i <> char '>'
    pp (IntType False i) = text "uint" <> char '<' <> pp i <> char '>'
    pp BoolType          = text "bool"
    pp (UserType n)      = pp n
    pp (EnumType es)     = text "enum" <+> (braces $ nest' $ vcat $ punctuate comma $ map ppenum es)
                               where ppenum (n,Nothing) = pp n
                                     ppenum (n, Just e) = pp n <+> char '=' <+> pp e
    pp (StructType fs)   = text "struct" <+> (braces $ nest' $ vcat $ map ((<> semi) . ppfield) fs)
                               where ppfield (t,n) = pp t <+> pp n
    pp (ArrayType t e)   = pp t <> (brackets $ pp e)


type PType = AtPos Type
type TypeName = PString

-- Template
data Template = Template PString
                         [TemplateImport] 
                         [(Bool, PTemplateItem)] -- export?, item
instance PP Template where
    pp (Template n imps items) = text "template" <+> pp n <+> ppimports imps $+$ 
                                 ppitems items $+$ 
                                 text "endtemplate"
        where ppimports [] = text ""
              ppimports imps = parens $ hsep $ punctuate comma $ map pp imps
              ppitems items = vcat $ map ((<> semi) . ppitem) items
              ppitem (True, i) = text "export" <+> pp i
              ppitem (False, i) = pp i
type PTemplate = AtPos Template

type TemplateImport = (TemplateName, PString)
instance PP TemplateImport where
    pp (t,n) = pp t <+> pp n
type TemplateName = PString

data TemplateItem = TDerive        TemplateName
                  | TTypeDecl      TypeDef
                  | TConstDecl     ConstDef
                  | TVarDecl       Visibility VarDecl
                  | TInitBlock     PStatement
                  | TProcessDecl   PString PStatement
                  | TTaskDecl      TaskCat                                                 -- category
                                   Signature
                                   (Either (Maybe PStatement,Maybe PStatement) PStatement) -- body: either before/after blocks or the actual implementation
                  | TFunctionDecl  Signature (Maybe PStatement)
                  | TProcedureDecl Signature (Maybe PStatement)
                  | TGoalDecl      PString PGoal
                  | TAssign        PLExpr PExpr                                            -- Continuous assignment
instance PP TemplateItem where
    pp (TDerive n) = text "derive" <+> pp n
    pp (TTypeDecl t) = pp t
    pp (TConstDecl c) = pp c
    pp (TVarDecl v decl) = pp v <+> pp decl
    pp (TInitBlock s) = text "init" $+$ pp s
    pp (TProcessDecl n s) = (text "process" <+> pp n) $+$ pp s
    pp (TTaskDecl c sig (Left (bef,aft))) = (text "task" <+> pp c <+> pp sig) $+$
                                            case bef of 
                                                 Nothing -> empty
                                                 Just s -> text "before" $+$ pp s
                                            $+$
                                            case aft of
                                                 Nothing -> empty
                                                 Just s -> text "after" $+$ pp s
    pp (TTaskDecl c sig (Right s)) = (text "task" <+> pp c <+> pp sig) $+$ pp s
    pp (TFunctionDecl sig body) = (text "function" <+> pp sig) $+$ pp body
    pp (TProcedureDecl sig body) = (text "procedure" <+> pp sig) $+$ pp body
    pp (TGoalDecl n g) = text "goal" <+> pp n <+> char '=' <+> pp g
    pp (TAssign l r) = text "assign" <+> pp l <+> char '=' <+> pp r
                                                 
type PTemplateItem = AtPos TemplateItem

data VarDecl = VarDecl PType PString (Maybe PExpr)
instance PP VarDecl where
    pp (VarDecl t n Nothing) = pp t <+> pp n
    pp (VarDecl t n (Just e)) = pp t <+> pp n <+> char '=' <+> pp e

data Signature = Signature (Maybe PType) PString [PArg]  -- ret type, args, body
instance PP Signature where
    pp (Signature ret n args) = pp ret <+> pp n <+> (parens $ hsep $ punctuate comma $ map pp args)

data Arg = Arg ArgDir PType PString                      -- direction, type, name
instance PP Arg where
    pp (Arg dir t n) = pp dir <+> pp t <+> pp n
type PArg = AtPos Arg

type MethodName = PIdent

data Visibility = VarVis | VarInvis
instance PP Visibility where
    pp VarVis   = empty
    pp VarInvis = text "invisible"

-- Statements
data Statement = SVarDecl VarDecl
               | SReturn PExpr
               | SSeq [PStatement]
               | SPar [PStatement] 
               | SForever PStatement
               | SDo PStatement PExpr
               | SWhile PExpr PStatement
               | SFor (Maybe PStatement, PExpr, PStatement) PStatement
               | SChoice [PStatement]
               | SPause
               | SStop
               | SInvoke MethodName [PExpr]
               | SAssert PExpr
               | SAssume PExpr
               | SAssign PLExpr PExpr
               | SITE PExpr PStatement (Maybe PStatement)     -- if () then {..} [else {..}]
               | SCase PExpr [(PExpr, PStatement)] (Maybe PStatement)
               | SMagic (Either GoalName PExpr)
instance PP Statement where
    pp (SVarDecl d)               = pp d
    pp (SReturn e)                = text "return" <+> pp e
    pp (SSeq ss)                  = braces' $ vcat $ map ((<> semi) . pp) ss
    pp (SPar ss)                  = text "fork" $+$ (braces' $ vcat $ map ((<> semi) . pp) ss)
    pp (SForever s)               = text "forever" $+$ pp s
    pp (SDo s cond)               = text "do" $+$ pp s <+> text "while" <+> (parens $ pp cond)
    pp (SWhile cond s)            = (text "while" <+> (parens $ pp cond)) $+$ pp s
    pp (SFor (init, cond, upd) s) = (text "for" <+> (parens $ pp init <> semi <+> pp cond <> semi <+> pp upd)) $+$ pp s
    pp (SChoice ss)               = text "choice" $+$ (braces' $ vcat $ map ((<> semi) . pp) ss)
    pp SPause                     = text "pause"
    pp SStop                      = text "stop"
    pp (SInvoke m args)           = pp m <+> (parens $ hsep $ punctuate comma $ map pp args)
    pp (SAssert e)                = text "assert" <+> (parens $ pp e)
    pp (SAssume e)                = text "assume" <+> (parens $ pp e)
    pp (SAssign l r)              = pp l <+> char '=' <+> pp r
    pp (SITE cond s1 ms2)         = text "if" <+> (parens $ pp cond) $+$ pp s1 $+$
                                    (case ms2 of
                                          Nothing -> empty
                                          Just s2 -> text "else" $+$ pp s2)
    pp (SCase e cases def)        = text "case" <+> (parens $ pp e) <+> (braces' $ ppcases $+$ ppdef)
                                         where ppcases = vcat $ map (\(c,s) -> pp c <> colon <+> pp s <> semi) cases
                                               ppdef = case def of 
                                                            Nothing -> empty
                                                            Just s  -> text "default" <> colon <+> pp s <> semi
    pp (SMagic (Left g))          = (braces $ text "...") <+> text "using" <+> pp g
    pp (SMagic (Right c))         = (braces $ text "...") <+> text "post" <+> pp c

type PStatement = AtPos Statement
type GoalName = PString

-- Expressions 
data Expr = ETerm PIdent
          | ELit (Maybe Int) Radix Integer  -- width, radix, value
          | EBool Bool
          | EApply MethodName [PExpr]
          | EUnOp UOp PExpr
          | EBinOp BOp PExpr PExpr
          | ETernOp PExpr PExpr PExpr
          | ECase PExpr [(PExpr, PExpr)] (Maybe PExpr)
          | ECond [(PExpr, PExpr)] (Maybe PExpr)
          | ESlice Slice PExpr
          | EStruct TypeName (Either [(PString, PExpr)] [PExpr]) -- either named or anonymous list of fields
          | ENonDet
instance PP Expr where
    pp (ETerm i)            = pp i
    pp (ELit w r v)         = pp w <> pp r <> 
                              case r of
                                   Rad2  -> text $ showIntAtBase 2 intToDigit v ""
                                   Rad8  -> text $ showOct v ""
                                   Rad10 -> pp v
                                   Rad16 -> text $ showHex v ""
    pp (EBool True)          = text "true"
    pp (EBool False)         = text "false"
    pp (EApply m args)       = pp m <+> (parens $ hsep $ punctuate comma $ map pp args)
    pp (EUnOp op e)          = parens $ pp op <> pp e
    pp (EBinOp op e1 e2)     = parens $ pp e1 <+> pp op <+> pp e2
    pp (ETernOp c e1 e2)     = parens $ pp c <+> char '?' <+> pp e2 <+> colon <+> pp e2
    pp (ECase e cs def)      = text "case" <+> (parens $ pp e) <+> (braces' $ ppcs $+$ ppdef)
                                   where ppcs = vcat $ map (\(c,e') -> pp c <> colon <+> pp e' <> semi) cs
                                         ppdef = text "default" <> colon <+> pp def <> semi
    pp (ECond cs def)        = text "cond" <+> (braces' $ ppcs $+$ ppdef)
                                   where ppcs = vcat $ map (\(c,e') -> pp c <> colon <+> pp e' <> semi) cs
                                         ppdef = text "default" <> colon <+> pp def <> semi
    pp (ESlice s e)          = pp e <> pp s
    pp (EStruct t (Left fs)) = pp t <+> (braces $ hcat $ punctuate comma $ 
                                         map (\(n,e) -> char '.' <> pp n <+> char '=' <+> pp e) fs)
    pp (EStruct t (Right fs)) = pp t <+> (braces' $ vcat $ punctuate comma $ map pp fs)
    pp ENonDet                = char '*'
type PExpr = AtPos Expr

type ConstExpr = Expr
type PConstExpr = PExpr

data LExpr = LExpr PIdent (Maybe Slice)  -- lhs expression
instance PP LExpr where
    pp (LExpr i Nothing)  = pp i
    pp (LExpr i (Just s)) = pp i <> pp s
type PLExpr = AtPos LExpr

data UOp = UMinus 
         | Not 
         | BNeg
instance PP UOp where
    pp UMinus = char '-'
    pp Not    = char '!'
    pp BNeg   = char '~'

data BOp = Eq 
         | Neq 
         | Lt 
         | Gt 
         | Lte 
         | Gte
         | And 
         | Or 
         | Imp
         | BAnd 
         | BOr 
         | BXor
         | Plus 
         | BinMinus 
         | Mod
         | Mul
instance PP BOp where
    pp Eq       = text "=="
    pp Neq      = text "!="
    pp Lt       = text "<"
    pp Gt       = text ">"
    pp Lte      = text "<="
    pp Gte      = text ">="
    pp And      = text "&&"
    pp Or       = text "||"
    pp Imp      = text "->"
    pp BAnd     = text "&"
    pp BOr      = text "|"
    pp BXor     = text "^"
    pp Plus     = text "+"
    pp BinMinus = text "-"
    pp Mod      = text "%"
    pp Mul      = text "*"


-- Goals
type Goal = Expr
type PGoal = AtPos Goal
