-- Parsed TSL spec

module ParsedSpec() where

-- A TSL spec is a list of type, constant, and template declarations
type Spec = [SpecItem]
data SpecItem = TypeDecl     String Type
              | ConstDecl    String ConstExpr
              | TemplateDecl String Template

-- Type declaration
data Type = IntType Int Bool                     -- width, signed/unsigned
          | BoolType
          | UserType String                      -- name of a user-defined type
          | EnumType [(String, Maybe ConstExpr)]
          | StructType [(String, Type)]
          | ArrayType Type ConstExpr             -- element type, length

type TypeName = String

-- Template
data Template = Template [TemplateImport] [TemplateItem]
type TemplateImport = (TemplateName, String)
type TemplateName = String

data TemplateItem = TDerive      TemplateName
                  | TTypeDecl    String Type
                  | TConstDecl   String ConstExpr
                  | TVarDecl     Bool String Type                                 -- export?, name, type
                  | TInitBlock   Statement
                  | TProcessDecl String Statement
                  | TTaskDecl    Bool String TaskCat (Maybe Type) [Arg] Statement -- export?, category, optional ret type, args, body
                  | TFuncDecl    Bool String Type [Arg] Statement                 -- export?, ret type, args, body
                  | TProcDecl    Bool String (Maybe Type) [Arg] Statement         -- export?, optional ret type, args, body
                  | TGoalDecl    String Goal
                  | TAssign      LExpr Expr                                       -- Continuous assignment

data TaskCat = Contr | Uncontr | Invis

type MethodName = Ident

-- Statements
data Statement = SVarDecl String Type
               | SSeq [Statement]
               | SPar [Statement] 
               | SForever Statement
               | SDo Statement Expr
               | SWhile Expr Statement
               | SFor Statement Expr Statement Statement
               | SChoice [Statement]
               | SPause
               | SStop
               | SInvoke MethodName [Expr]
               | SAssert Expr
               | SAssume Expr
               | SAssign LExpr Expr
               | SITE Expr Statement (Maybe Statement)     -- if () then {..} [else {..}]
               | SCase Expr [(Expr, Statement)]
               | SInvocation MethodName [Expression]
               | SMagic (Either GoalName Expr)

type GoalName = String

-- Expressions 
data Expr = ETerm Ident
          | ELit Int Radix Integer  -- width, radix, value
          | ETopBot Bool
          | EApply MethodName [Expr]
          | EUnOp UOp Expr
          | EBinOp BOp Expr Expr
          | ETernOp Expr Expr Expr
          | ECase Expr [(Expr, Expr)]
          | ECond [(Expr, Expr)]
          | ESlice Expr Slice
          | EStruct TypeName [(FieldName, Expr)]

type ConstExpr = Expr
data LExpr = LExpr Ident (Maybe Slice)  -- lhs expression

type Slice = (Int, Int)  -- low,high

data Radix = Rad2 | Rad8 | Rad10 | Rad16

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
