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

  -- builtin types
  'uint'                      { L (UINT $$) _ }
  'bytes'                     { L (BYTES $$) _ }
  'address'                   { L ADDRESS _ }
  'bool'                      { L BOOL _ }
  'string'                    { L STRING _ }

  -- symbols
  break                          { L BREAK _ }
  ':='                        { L ASSIGN _ }
  '=>'                        { L ARROW _ }
  -- '->'                        { L ARROW' _ }
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

%%

ACT : list(Transition)                                { () }

Transition : 'behaviour' id 'of' id
             'interface' id '(' seplist(Decl, ',') ')'
             opt(Precondition)
             Claim                                    { () }

Claim : 'storage' list(Store)                         { () }
      | 'returns' Expr                                { () }
      | 'storage' list(Store) 'returns' Expr          { () }

Precondition : 'iff' list(Expr)                            { () }
             | 'iff in range' list(Expr)                   { () }
             | 'iff' list(Expr) 'iff in range' list(Expr)  { () }
             | 'iff in range' list(Expr) 'iff' list(Expr)  { () }

Store : Expr '=>' Expr                                { ($1, $3) }

Creation : 'creates' break seplist(Init, break)       { Creates $3 [] }

Init : Decl ':=' Expr                                 { Init $1 $3 }

Decl : Type id                                        { Decl $1 (Id $2) }

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
     | 'mapping' '(' Type '=>' Type ')'               { T_map $3 $5 }
     | 'address'                                      { T_address }
     | 'bool'                                         { T_bool }
     | 'string'                                       { T_string }

Expr : ilit                                           { IntLit $1 }

-- parameterized productions

seplist(x, sep) : x                                   { [$1]    }
                | seplist(x, sep) sep x               { $3 : $1 }

list(x) : x                                           { [$1]    }
        | list(x) x                                   { $2 : $1 }

opt(x) : x                                            { Just $1 }
       | {- empty -}                                  { Nothing }

{

validsize :: Int -> Bool
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> Except String a
parseError tokens =
  case (head tokens) of
  L token posn -> throwError $ concat [
    "parse error on ",
    show token,
    " at ",
    showposn posn]

main = do
  contents <- getContents
  let tree = parse $ lexer contents
  print tree
}