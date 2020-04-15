{
module Main where
import Prelude hiding (EQ, GT, LT)
import Lex
import Syntax
import Control.Monad.Except
}

%name parse
%monad { Except String } { (>>=) } { return }
%tokentype { Lexeme }
%error { parseError }

%token

  eof                         { L EOF _ }

  -- reserved words
  'behaviour'                 { L BEHAVIOUR _ }
  'of'                        { L OF _ }
  'interface'                 { L INTERFACE _ }
  'constructor'               { L CONSTRUCTOR _ }
  'creates'                   { L CREATES _ }
  'case'                      { L CASE _ }
  'returns'                   { L RETURNS _ }
  'storage'                   { L STORAGE _ }
  'noop'                      { L NOOP _ }
  'iff in range'              { L IFFINRANGE _ }
  'iff'                       { L IFF _ }
  'and'                       { L AND _ }
  'or'                        { L OR _ }
  'true'                      { L TRUE _ }
  'false'                     { L FALSE _ }
  'mapping'                   { L MAPPING _ }
  'if'                        { L IF _ }
  'then'                      { L THEN _ }
  'else'                      { L ELSE _ }

  -- builtin types
  'uint'                      { L (UINT $$) _ }
  'bytes'                     { L (BYTES $$) _ }
  'address'                   { L ADDRESS _ }
  'bool'                      { L BOOL _ }
  'string'                    { L STRING _ }

  -- symbols
  break                       { L BREAK _ }
  ':='                        { L ASSIGN _ }
  '=>'                        { L ARROW _ }
  '=='                        { L EQEQ _ }
  '=/='                       { L NEQ _ }
  '>='                        { L GE _ }
  '<='                        { L LE _ }
  '++'                        { L CAT _ }
  '..'                        { L SLICE _ }
  '('                         { L LPAREN _ }
  ')'                         { L RPAREN _ }
  '['                         { L LBRACK _ }
  ']'                         { L RBRACK _ }
  '='                         { L EQ _ }
  '>'                         { L GT _ }
  '<'                         { L LT _ }
  ':'                         { L COLON _ }
  '+'                         { L PLUS _ }
  '-'                         { L MINUS _ }
  '*'                         { L STAR _ }
  '/'                         { L SLASH _ }
  '%'                         { L MOD _ }
  '^'                         { L CARROT _ }
  '_'                         { L SCORE _ }
  '.'                         { L DOT _ }
  ','                         { L COMMA _ }

  id                          { L (ID $$) _ }

  ilit                        { L (ILIT $$) _ }


-- associativity and precedence (wip) --

%nonassoc '=>'
%nonassoc 'if' 'then' 'else'

%left 'and'
%left 'or'

%left '+' '-'
%left '*' '/'
%nonassoc '%'
%right '^'

%nonassoc '<=' '<' '>=' '>' '==' '=/='

%%

ACT : list(Transition)                                { $1 }


-- parameterized productions --

pair(a,b) : a b                                       { ($1,$2) }

seplist(x, sep) : x                                   { [$1]    }
                | seplist(x, sep) sep x               { $3 : $1 }

nonempty(x) : x                                       { [$1]    }
            | nonempty(x) x                           { $2 : $1 }

list(x) : {- empty -}                                 { []      }
        | list(x) x                                   { $2 : $1 }

opt(x) : x                                            { Just $1 }
       | {- empty -}                                  { Nothing }


-- rules --

Transition : 'behaviour' id 'of' id
             Interface
             list(Precondition)
             Cases
             opt(Ensures)                             { Transition $2 $4 $5 $6 $7 $8 }

Ensures : nonempty(Expr)                              { $1 }

Interface : 'interface' id '(' seplist(Decl, ',') ')' { Interface $2 $4 }

Case : 'case' Expr ':'                                { $2 }

Cases : Post                                          { TDirect $1 }
      | nonempty(pair(Case,Post))                     { TCases $1 }

Post : opt(Storage) list(ExtStorage) opt(Returns)     { Post $1 $2 $3 }

Returns : 'returns' Expr                              { $2 }

Storage : 'storage' nonempty(Store)                   { $2 }

ExtStorage : 'storage' id break nonempty(Store)       { ExtStorage $2 $4 }
--           | 'creates' id break nonempty(Store)       { ExtCreates $2 $4 }

Precondition : 'iff' nonempty(Expr)                   { Iff $2 }
             | 'iff in range' Type nonempty(Expr)     { IffIn $2 $3 }

Store : Entry '=>' Expr                               { ($1, $3) }

Entry : id list(Expr)                                 { Entry $1 $2 }

--Creation : 'creates' break seplist(Init, break)       { Creates $3 [] }
--
--Init : Decl ':=' Expr                                 { Init $1 $3 }
--
Decl : Type id                                        { Decl $1 $2 }

Type : 'uint'
       { case validsize $1 of
              True  -> T_uint $1 
              False -> error "invalid uint size"
       }
     | 'bytes'
       { case validsize $1 of
              True  -> T_bytes $1
              False -> error "invalid bytes size"
       }
     | Type '[' ilit ']'                              { T_array_static $1 $3 }
     | 'address'                                      { T_address }
     | 'bool'                                         { T_bool }
     | 'string'                                       { T_string }

Container : 'mapping' '(' Type '=>' Container ')'     { Mapping $3 $5 }
          | Type                                      { Direct $1 }
Expr :

    '(' Expr ')'                                        { $2 }

  -- terminals
  | id                                                  { Var $1 }
  | ilit                                                { IntLit $1 }
  -- missing string literal
  -- missing wildcard

  -- boolean expressions
  | Expr 'and' Expr                                     { EAnd   $1 $3 }
  | Expr 'or'  Expr                                     { EOr    $1 $3 }
  | Expr '=>'  Expr                                     { EImpl  $1 $3 }
  | Expr '=='  Expr                                     { EEq    $1 $3 }
  | Expr '=/=' Expr                                     { ENeq   $1 $3 }
  | Expr '<='  Expr                                     { ELEQ   $1 $3 }
  | Expr '<'   Expr                                     { ELT    $1 $3 }
  | Expr '>='  Expr                                     { EGEQ   $1 $3 }
  | Expr '>'   Expr                                     { EGT    $1 $3 }
  | 'true'                                              { ETrue        }
  | 'false'                                             { EFalse       }

  -- integer expressions
  | Expr '+'   Expr                                     { EAdd   $1 $3 }
  | Expr '-'   Expr                                     { ESub   $1 $3 }
  | Expr '*'   Expr                                     { EMul   $1 $3 }
  | Expr '/'   Expr                                     { EDiv   $1 $3 }
  | Expr '%'   Expr                                     { EMod   $1 $3 }
  | Expr '^'   Expr                                     { EExp   $1 $3 }

  -- composites
  | 'if' Expr 'then' Expr 'else' Expr                   { EITE $2 $4 $6 }
{-
  | id '[' Expr ']'                                     { Look $1 $3 }
  | id '(' seplist(Expr, ',') ')'                       { App $1 $3 }
  | Expr '++' Expr                                      { ECat $1 $3 }
  | id '[' Expr '..' Expr ']'                           { ESlice $1 $3 $5 }
-}
  -- missing builtins

{

validsize :: Int -> Bool
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> Except String arror
parseError [] = throwError "no valid tokens"
parseError ((L token posn):tokens) =
  throwError $ concat [
    "parse error on ",
    show token,
    " at ",
    showposn posn]

main = do
  contents <- getContents
  let tree = parse $ lexer contents
  print tree
}
