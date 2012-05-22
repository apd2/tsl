module Main where

import Control.Applicative

import Text.Parsec hiding ((<|>))
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

import TSLSyntax

reservedOpNames = ["!", "~", "&", "|", "^", "->", "||", "&&", "=", "==", "!="]
reservedNames = ["assert",
                 "assign",
                 "assume", 
                 "case",
                 "choice", 
                 "controllable", 
                 "default",
                 "do", 
                 "else", 
                 "endtemplate",
                 "export",
                 "forever", 
                 "fork", 
                 "function", 
                 "goal",
                 "if", 
                 "invisiblae", 
                 "pause",
                 "post", 
                 "procedure", 
                 "process",
                 "stop", 
                 "switch",
                 "task", 
                 "template", 
                 "typedef",
                 "uncontrollable", 
                 "using", 
                 "while"]

lexer = T.makeTokenParser (emptyDef {T.commentStart      = "/*"
                                    ,T.commentEnd        = "*/"
                                    ,T.commentLine       = "//"
                                    ,T.nestedComments    = True
                                    ,T.identStart        = letter <|> char '_'
                                    ,T.identLetter       = alphaNum <|> char '_'
                                    ,T.reservedOpNames   = reservedOpNames
                                    ,T.reservedNames     = reservedNames
                                    ,T.caseSensitive     = True})

reservedOp = T.reservedOp lexer
reserved   = T.reserved lexer
identifier = T.identifier lexer
semiSep    = T.semiSep lexer
semiSep1   = T.semiSep1 lexer
colon      = T.colon lexer
commaSep   = T.commaSep lexer
commaSep1  = T.commaSep1 lexer
symbol     = T.symbol lexer
semi       = T.semi lexer
comma      = T.comma lexer
braces     = T.braces lexer
parens     = T.parens lexer
angles     = T.angles lexer
brackets   = T.brackets lexer
natural    = T.natural lexer
integer    = T.integer lexer
whiteSpace = T.whiteSpace lexer
lexeme     = T.lexeme lexer
dot        = T.dot lexer
stringLit  = T.stringLiteral lexer

-- A TSL spec is a list of template, type, and constant declarations.  
tslSpec = many decl
decl = templateDecl <|> typeDecl <|> constDecl

-- Type declarations
typeDecl = reserved "template"


quote :: String -> String
quote s = "\"" ++ s ++ "\""

ident = identifier <|> 
        quote <$> stringLit

fieldSelector = Field <$ dot <*> ident
indexSelector = Index <$> brackets expr
sym = Ident <$> ident <*> many (fieldSelector <|> indexSelector)

slice = brackets $ f <$> natural <*> (colon *> natural)
    where f l r = (fromIntegral r, fromIntegral l)





main = putStrLn "TSL v2 parser"
