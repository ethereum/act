{-

  this is a happy grammar :)

  14 shift/reduce conflicts in a single state are expected, due
  to the ambiguity of if/then/else expressions.

 -}

{

module Parse (parse) where

import Prelude hiding (EQ, GT, LT)
import Data.Functor.Foldable
import Data.Functor.Product
import Data.Functor.Const
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
  'creator'                   { L CREATOR _ }
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
  'not'                       { L NOT _ }
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
  uint                        { L (UINT _) _ }
  int                         { L (INT _) _ }
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

  id                          { L (ID _) _ }

  ilit                        { L (ILIT _) _ }


{- --- associativity and precedence ---

  boolean operations have universally lower precedence than numeric
  operations
  
  no operators are right associative
  
  some examples:
  `a == b and not c == d` should parse as `(a == b) and (not (c == d))`
  `a * b ^ c % d` should parse as `a * ((b ^ c) % d)`

 -}

-- boolean
%left 'and' 'or'
%nonassoc 'not'
%left '==' '=/='
%nonassoc '<=' '<' '>=' '>'

-- numeric
%left '+' '-'
%left '*' '/'
%nonassoc '%'
%left '^'

%%

Act : RawConstructor list(RawBehaviour)             { Act $1 $2 }

-- parameterized productions --

pair(a, b) : a b                                    { ($1, $2) }

list(x) : {- empty -}                               { []      }
        | list(x) x                                 { $2 : $1 }

seplist(x, sep) : {- empty -}                       { []      }
                | x                                 { [$1]    }
                | seplist(x, sep) sep x             { $3 : $1 }

opt(x) : x                                          { Just $1 }
       | {- empty -}                                { Nothing }



-- rules --

RawConstructor : 'creator' 'of' id Interface Creates
  { RawConstructor (getid $3) $4 $5 Nothing    @@  lpos $1 }
               | 'creator' 'of' id Interface Creates Claim
  { RawConstructor (getid $3) $4 $5 (Just $6)  @@  lpos $1 }

RawBehaviour : 'behaviour' id 'of' id
               Interface
               opt(Precondition)
               list(Case)
  { RawBehaviour (getid $2) (getid $4) $5 $6 $7  @@  lpos $1 }

Interface : 'interface' id '(' seplist(Decl, ',') ')'
  { Interface (getid $2) $4  @@  lpos $1 }

Creates : 'creates' list(Creation)      { $2 }

Creation : Defn                         { CDefn $1  @@  snd $1 }
         | Decl                         { CDecl $1  @@  snd $1 }

Precondition : 'iff' list(Expr)         { $2 }

Case : 'case' Expr ':' list(Claim)      { Case $2 $4  @@  lpos $1 }

Claim : 'storage' list(Store)           { StorageClaim $2  @@  lpos $1 }
      | 'returns' Expr                  { ReturnClaim $2   @@  lpos $1 }

Store : Expr '=>' Expr                  { Store $1 $3  @@  npos $1 }
      
Defn : Type id ':=' Expr                { Defn $1 (getid $2) $4 @@ npos $1 }

Decl : Type id                          { Decl $1 (getid $2)  @@  npos $1 }

-- we welcome all kinds here
-- prejudice is the job of the typechecker
Type : uint {
         case validsize (uintSize $1) of
              True  -> TUInt (uintSize $1)  @@@  lpos $1
              False -> error "invalid uint size"
       }
     | int {
         case validsize (intSize $1) of
              True  -> TInt (intSize $1)  @@@  lpos $1
              False -> error "invalid int size"
       }
     | 'address'                        { TAddress        @@@  lpos $1 }
     | 'bool'                           { TBool           @@@  lpos $1 }
     | 'mapping' '(' Type '=>' Type ')' { TMapping $3 $5  @@@  lpos $1 }

Ref : id                        { Ref (getid $1)      @@  lpos $1 }
    | id '[' Expr ']'           { Zoom (getid $1) $3  @@  lpos $1 }

Expr:

    '(' Expr ')'                { $2 }

  -- booleans
  | 'true'                      { EBoolLit True   @@@  lpos $1 }
  | 'false'                     { EBoolLit False  @@@  lpos $1 }
  | Expr 'and' Expr             { EAnd $1 $3      @@@  npos $1 }
  | Expr 'or' Expr              { EOr $1 $3       @@@  npos $1 }
  | 'not' Expr                  { ENot $2         @@@  lpos $1 }
  | Expr '==' Expr              { EEq $1 $3       @@@  npos $1 }
  | Expr '=/=' Expr             { ENeq $1 $3      @@@  npos $1 }
  | Expr '<=' Expr              { ELE $1 $3       @@@  npos $1 } 
  | Expr '<' Expr               { ELT $1 $3       @@@  npos $1 }
  | Expr '>=' Expr              { EGE $1 $3       @@@  npos $1 }
  | Expr '>' Expr               { EGT $1 $3       @@@  npos $1 }

  -- numbers
  | ilit
    { case $1 of (L (ILIT i) _) -> EIntLit i  @@@  lpos $1 }
  | Expr '+' Expr               { EAdd $1 $3  @@@  npos $1 }
  | Expr '-' Expr               { ESub $1 $3  @@@  npos $1 }
  | Expr '*' Expr               { EMul $1 $3  @@@  npos $1 }
  | Expr '/' Expr               { EDiv $1 $3  @@@  npos $1 }
  | Expr '%' Expr               { EMod $1 $3  @@@  npos $1 }
  | Expr '^' Expr               { EExp $1 $3  @@@  npos $1 }

  -- other
  | Ref                                 { ERead (fst $1)  @@@  snd $1  }
  | EthEnv                              { EEnv (fst $1)   @@@  snd $1  }
  | 'if' Expr 'then' Expr 'else' Expr   { EITE $2 $4 $6   @@@  lpos $1 }
  | '_'                                 { EScore          @@@  lpos $1 }

EthEnv : 
    'CALLER'                    { EnvCaller      @@  lpos $1 }
  | 'CALLVALUE'                 { EnvCallValue   @@  lpos $1 }
  | 'CALLDEPTH'                 { EnvCallDepth   @@  lpos $1 }
  | 'ORIGIN'                    { EnvOrigin      @@  lpos $1 }
  | 'BLOCKHASH'                 { EnvBlockHash   @@  lpos $1 }
  | 'BLOCKNUMBER'               { EnvBlockNumber @@  lpos $1 }
  | 'DIFFICULTY'                { EnvDifficulty  @@  lpos $1 }
  | 'CHAINID'                   { EnvChainID     @@  lpos $1 }
  | 'GASLIMIT'                  { EnvGasLimit    @@  lpos $1 }
  | 'COINBASE'                  { EnvCoinbase    @@  lpos $1 }
  | 'TIMESTAMP'                 { EnvTimestamp   @@  lpos $1 }
  | 'THIS'                      { EnvAddress     @@  lpos $1 }
  | 'NONCE'                     { EnvNonce       @@  lpos $1 }
{

-- utility functions
getid (L (ID s) _) = s
uintSize (L (UINT size) _) = size
intSize (L (INT size) _) = size
lpos (L _ p) = p                    -- get lexeme position
npos (Fix (Pair _ c)) = getConst c  -- get node position
e @@@ p = Fix $ Pair e (Const p)
(@@) = (,)
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> Either String a
parseError [] = Left "parse error: empty program"
parseError ((L token posn):_) = Left $ concat
    [ "parse error: ", show token, " at ", show posn ]

}
