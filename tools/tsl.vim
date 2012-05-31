" Vim syntax file
" Language:	TSL (Termite Specification Language)
" Filenames:    *.tsl
"
" Place this file (or a link to it) under ~/.vim/syntax and add
" the following line to your .vimrc to enable syntax highlighting 
" automatically for TSL files:
" au BufRead,BufNewFile *.tsl             set filetype=tsl

syn clear

syn case match

"C includes
syn match  cInclude             display "^\s*\(%:\|#\)\s*include\>\s*["<]"


"Comments in LOTOS are between (* and *)
syn region tslComment	start="/\*"  end="\*/" contains=tslTodo
syn region tslComment   start="//" skip="\\$" end="$" keepend contains=tslTodo

"Operators !, ?, ~, &, |, ^, ->, ||, &&, =, ==, !=, <, <=, >, >=, %, +, -, *, ...
syn match  tslDelimiter         "||"
syn match  tslDelimiter         "&&"
syn match  tslDelimiter         "=="
syn match  tslDelimiter         "!="
syn match  tslDelimiter         ">="
syn match  tslDelimiter         "<="
syn match  tslDelimiter         "\.\.\."
syn match  tslDelimiter         "\*"
syn match  tslDelimiter	        "[\[\]!?\~&|\^=<>%+-,;\:\.]"

"Regular keywords
syn keyword tslStatement	after assert assign assume before choice default derive 
syn keyword tslStatement	endtemplate fork function goal import init know out 
syn keyword tslStatement	pause post procedure process return stop switch task template 
syn keyword tslStatement	using 


syn keyword tslTodo             contained TODO FIXME XXX

"Loops
syn keyword tslRepeat           do while for forever

"Conditionals
syn keyword tslConditional      if else cond case

"Constants
syn keyword tslConstant         true false 

"Storage class
syn keyword tslStorageClass     const controllable uncontrollable invisible export

"Operators from the Abstract Data Types in IS8807
syn keyword tslOperator	        default true false

"Keywords for ADTs
syn keyword tslType	        bool uint sint stuct enum void typedef

syn sync lines=250

" Verilog-style numeric literals
syn match tslNumber "\(\<\d\+\|\)'[sS]\?[bB]\s*[0-1?]\+\>"
syn match tslNumber "\(\<\d\+\|\)'[sS]\?[oO]\s*[0-7?]\+\>"
syn match tslNumber "\(\<\d\+\|\)'[sS]\?[dD]\s*[0-9?]\+\>"
syn match tslNumber "\(\<\d\+\|\)'[sS]\?[hH]\s*[0-9a-fA-F?]\+\>"
syn match tslNumber "\<[+-]\=[0-9]\+\(\.[0-9]*\|\)\(e[0-9]*\|\)\>"


if !exists("did_tsl_syntax_inits")
  let did_tsl_syntax_inits = 1
  hi link tslStatement		Statement
  hi link tslOperator		Operator
  hi link tslType		Type
  hi link tslComment		Comment
  hi link tslDelimiter          String
  hi link tslConstant           Constant
  hi link tslRepeat             Repeat
  hi link tslConditional        Conditional
  hi link tslTodo               Todo
  hi link tslNumber             Number
  hi link tslStorageClass       StorageClass
  hi link cInclude              String
endif

let b:current_syntax = "tsl"

" vim: ts=8
