{
module Main where
import Prelude hiding (EQ, GT, LT)
import Lex
import Syntax
}

%name parse
%tokentype { Lexeme }
%error { parseError }

%token

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


ACT : Transition { $1 }

Transition : 'behaviour' id 'of' id break
             'interface' id '(' list(Decl, ',') ')' break
             'iff' break list(Expr, break) break
             {- Claim break -}                              { () }

Claim : 'storage' break list(Store, break)            { () }
      | 'returns' Expr                                { () }

Store : Expr '=>' Expr                { ($1, $3) }

Creation : 'creates' break list(Init, break)  { Creates $3 [] }

Init : Decl ':=' Expr              { Init $1 $3 }

Decl : Type id             { Decl $1 (Id $2) }

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
     | Type '[' ilit ']'                   { T_array_static $1 $3 }
     | 'mapping' '(' Type '=>' Type ')'    { T_map $3 $5 }
     | 'address'                           { T_address }
     | 'bool'                              { T_bool }
     | 'string'                            { T_string }

Expr : ilit                                { IntLit $1 }

-- parameterized productions

list(x, sep) : x                          { [$1]    }
             | list(x, sep) sep x         { $3 : $1 }

opt(x) : x                                { Just $1 }
       | {- empty -}                      { Nothing }


{

validsize :: Int -> Bool
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> a
parseError xs = error "parse error"

main = do
  contents <- getContents
  print $ alexScanTokens contents
  let tree = parse $ alexScanTokens contents
  print tree
}