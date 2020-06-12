{
module Parse where
import Prelude hiding (EQ, GT, LT)
import Lex
import Syntax
}

%name parse
%monad { Either String } { (>>=) } { return }
%tokentype { Lexeme }
%error { parseError }

%token

  eof                         { L EOF _ }

  -- reserved words
  'behaviour'                 { L BEHAVIOUR _ }
  'constructor'               { L CONSTRUCTOR _ }
  'of'                        { L OF _ }
  'interface'                 { L INTERFACE _ }
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
  'ensures'                   { L ENSURES _ }
  'invariants'                { L INVARIANTS _ }
  'if'                        { L IF _ }
  'then'                      { L THEN _ }
  'else'                      { L ELSE _ }
  'at'                        { L AT _ }

  -- builtin types
  'uint'                      { L (UINT $$) _ }
  'int'                       { L (INT $$) _ }
  'bytes'                     { L (BYTES $$) _ }
  'address'                   { L ADDRESS _ }
  'bool'                      { L BOOL _ }
  'string'                    { L STRING _ }

  -- builtin functions
  'newAddr'                   { L NEWADDR _ }

  -- environment variables
  'CALLER'                    { L CALLER _ }
  'CALLVALUE'                 { L CALLVALUE _ }
  'CALLDEPTH'                 { L CALLDEPTH _ }
  'ORIGIN'                    { L ORIGIN _ }
  'BLOCKHASH'                 { L BLOCKHASH _ }
  'BLOCKNUMBER'               { L BLOCKNUMBER _ }
  'DIFFICULTY'                { L DIFFICULTY _ }
  'CHAINID'                   { L CHAINID _ }
  'GASLIMIT'                  { L GASLIMIT _ }
  'COINBASE'                  { L COINBASE _ }
  'TIMESTAMP'                 { L TIMESTAMP _ }
  'THIS'                      { L THIS _ }
  'NONCE'                     { L NONCE _ }

  
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
  '^'                         { L CARET _ }
  '_'                         { L SCORE _ }
  '.'                         { L DOT _ }
  ','                         { L COMMA _ }

  id                          { L (ID $$) _ }

  ilit                        { L (ILIT $$) _ }


-- associativity and precedence --

%nonassoc '==' '=/='
%left '+' '-'
%left '*' '/'

%%

ACT : list(Behaviour)                                 { $1 }


-- parameterized productions --

pair(a, b) : a b                                      { ($1, $2) }

list(x) : {- empty -}                                 { []      }
        | list(x) x                                   { $2 : $1 }

seplist(x, sep) : {- empty -}                         { []      }
                | x                                   { [$1]    }
                | seplist(x, sep) sep x               { $3 : $1 }

nonempty(x) : x                                       { [$1]    }
            | nonempty(x) x                           { $2 : $1 }

opt(x) : x                                            { Just $1 }
       | {- empty -}                                  { Nothing }


-- rules --

Behaviour : 'behaviour' id 'of' id 
            Interface
            opt(Precondition)
            list(Case)                      { Transition $2 $4 $5 $6 $7 }
          | 'constructor' id 'of' id
            Interface
            'creates' list(Creation)        { Constructor $2 $4 $5 $7 }
            
Interface : 'interface' id '(' seplist(Decl, ',') ')'  { Interface $2 $4 }

Precondition : 'iff' list(Expr)             { Precondition $2 }

Creation : Decl ':=' Expr                   { Creation $1 $3 }

Case : 'case' Expr ':' list(Claim)          { Case $2 $4 }

Claim : 'storage' list(Write)               { Storage $2 }
      | 'returns' Expr                      { Returns $2 }

Write : Address '=>' Expr                   { Write $1 $3 }

Address : id                                { Address $1 }

Decl : Type id                              { ($1, $2) }

Type : 'uint'                               { UInt }

Expr : -- numbers
       ilit                                 { EIntLit $1 }
     | Expr '+' Expr                        { EAdd $1 $3 }
     | Expr '*' Expr                        { EMul $1 $3 }
     | Expr '-' Expr                        { ESub $1 $3 }
     | Expr '/' Expr                        { EDiv $1 $3 }

     -- booleans
     | 'true'                               { EBooLit True }
     | 'false'                              { EBooLit False }
     | Expr '==' Expr                       { EEq $1 $3 }
     | Expr '=/=' Expr                      { ENeq $1 $3 }

     | '(' Expr ')'                         { $2 }

{

nowhere = AlexPn 0 0 0

validsize :: Int -> Bool
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> Either String a
parseError [] = Left "parse error: empty program"
parseError ((L token posn):_) = Left $ concat
    [ "parse error: ", show token, " at ", show posn ]

}
