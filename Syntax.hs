-- Parsed TSL spec

module Syntax where

import Text.Parsec.Pos

-- Element of a syntax tree with source position
data AtPos a = AtPos {getVal::a, getPos::SourcePos}
instance Functor AtPos where
    fmap f (AtPos x p) = AtPos (f x) p

-- Common types
type Slice = (Int, Int)  -- low,high
data Radix = Rad2 | Rad8 | Rad10 | Rad16
data ArgDir = ArgIn | ArgOut
data TaskCat = Contr | Uncontr | Invis

-- TSL identifier
type PString = AtPos String
data Selector = Field PString
              | Index PExpr
type PSelector = AtPos Selector
data Ident = Ident {root :: PString, path :: [PSelector]}
type PIdent = AtPos Ident


-- A TSL spec is a list of type, constant, and template declarations
type Spec = [PSpecItem]

data SpecItem = TypeDecl TypeDef
              | ConstDecl ConstDef
              | TemplateDecl PString PTemplate
type PSpecItem = AtPos SpecItem

data TypeDef = TypeDef PType PString
data ConstDef = ConstDef PType PString PConstExpr

-- Type declaration
data Type = IntType Bool Int                     -- signed/unsigned, width
          | BoolType
          | UserType PString                     -- name of a user-defined type
          | EnumType [(String, Maybe PConstExpr)]
          | StructType [(PType, PString)]
          | ArrayType PType PConstExpr           -- element type, length
type PType = AtPos Type
type TypeName = PString

-- Template
data Template = Template [TemplateImport] 
                         [(Bool, PTemplateItem)] -- export?, item
type PTemplate = AtPos Template

type TemplateImport = (TemplateName, PString)
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
                  | TFunctionDecl  Signature PStatement
                  | TProcedureDecl Signature PStatement
                  | TGoalDecl      PString PGoal
                  | TAssign        PLExpr PExpr                                            -- Continuous assignment
type PTemplateItem = AtPos TemplateItem

data VarDecl = VarDecl PType PString

data Signature = Signature (Maybe PType) PString [PArg]  -- ret type, args, body
data Arg = Arg ArgDir PType PString                      -- direction, type, name
type PArg = AtPos Arg

type MethodName = PIdent

data Visibility = VarVis | VarInvis

-- Statements
data Statement = SVarDecl VarDecl
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
type PStatement = AtPos Statement

type GoalName = PString

-- Expressions 
data Expr = ETerm PIdent
          | ELit Int Radix Integer  -- width, radix, value
          | EBool Bool
          | EApply MethodName [PExpr]
          | EUnOp UOp PExpr
          | EBinOp BOp PExpr PExpr
          | ETernOp PExpr PExpr PExpr
          | ECase PExpr [(PExpr, PExpr)]
          | ECond [(PExpr, PExpr)]
          | ESlice PExpr Slice
          | EStruct TypeName [(PString, PExpr)]
type PExpr = AtPos Expr

type ConstExpr = Expr
type PConstExpr = PExpr

data LExpr = LExpr PIdent (Maybe Slice)  -- lhs expression
type PLExpr = AtPos LExpr

data UOp = UMinus 
         | Not 
         | BNeg

data BOp = Eq 
         | Neq 
         | Lt 
         | Gt 
         | Lte 
         | Gte
         | And 
         | Or 
         | BAnd 
         | BOr 
         | BXor
         | Plus 
         | BinMinus 
         | Mod


-- Goals
type Goal = Expr
type PGoal = AtPos Goal
