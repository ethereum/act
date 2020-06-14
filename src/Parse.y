{-

  this is a happy grammar :)

 -}

{

module Parse where
import Prelude hiding (EQ, GT, LT)
import Lex
import EVM.ABI
import EVM.Solidity (SlotType(..))
import qualified Data.List.NonEmpty as NonEmpty
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
  'fi'                        { L FI _ }
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
  uint                        { L (UINT $$) _ }
  int                         { L (INT $$) _ }
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

Act : RawConstructor list(RawBehaviour)                     { Act $1 $2 }

-- parameterized productions --

pair(a, b) : a b                                        { ($1, $2) }

list(x) : {- empty -}                                   { []      }
        | list(x) x                                     { $2 : $1 }

seplist(x, sep) : {- empty -}                           { []      }
                | x                                     { [$1]    }
                | seplist(x, sep) sep x                 { $3 : $1 }

opt(x) : x                                              { Just $1 }
       | {- empty -}                                    { Nothing }


-- rules --

RawConstructor : 'constructor' id 'of' id Interface Creates
                                    { RawConstructor $2 $4 $5 $6 }

RawBehaviour : 'behaviour' id 'of' id
               Interface
               opt(Precondition)
               list(Case)           { RawBehaviour $2 $4 $5 $6 $7 }

Interface : 'interface' id '(' seplist(Decl, ',') ')'
                                            { Interface $2 $4 }

Creates : 'creates' list(Creation)          { $2 }

Creation : Defn                             { CDefn $1 }
         | Decl                             { CDecl $1 }

Precondition : 'iff' list(Expr)             { $2 }

Case : 'case' Expr ':' list(Claim)          { Case $2 $4 }

Claim : 'storage' list(Store)               { StorageClaim $2 }
      | 'returns' Expr                      { ReturnClaim $2 }

Store : Ref '=>' Expr                       { Store $1 $3 }
      
Ref : id                                    { Ref $1 }
    | id '[' Expr ']'                       { Zoom $1 $3 }

Defn : Type id ':=' Expr                    { Defn $1 $2 $4 }

Decl : Type id                              { Decl $1 $2 }

-- we don't distinguish between kinds here
-- that's the job of the typechecker
Type : uint
       { case validsize $1 of
              True  -> AbiType (AbiUIntType $1) 
              False -> error "invalid uint size"
       }
     | int
       { case validsize $1 of
              True  -> AbiType (AbiIntType $1)
              False -> error "invalid int size"
       }
     | 'address'                            { AbiType AbiAddressType }
     | 'bool'                               { AbiType AbiBoolType }
     | 'string'                             { AbiType AbiStringType }
     -- missing bytes
     -- missing arrays
     | 'mapping' '(' Type '=>' Type ')'     { Mapping $3 $5 }

Expr:

    '(' Expr ')'                            { $2 }

  -- booleans
  | 'true'                                  { EBoolLit True }
  | 'false'                                 { EBoolLit False }
  | Expr 'and' Expr                         { EAnd $1 $3 }
  | Expr 'or' Expr                          { EOr $1 $3 }
  | 'not' Expr                              { ENot $2 }
  | Expr '==' Expr                          { EEq $1 $3 }
  | Expr '=/=' Expr                         { ENeq $1 $3 }
  | Expr '<=' Expr                          { ELE $1 $3 } 
  | Expr '<' Expr                           { ELT $1 $3 }
  | Expr '>=' Expr                          { EGE $1 $3 }
  | Expr '>' Expr                           { EGT $1 $3 }

  -- numbers
  | ilit                                    { EIntLit $1 }
  | Expr '+' Expr                           { EAdd $1 $3 }
  | Expr '-' Expr                           { ESub $1 $3 }
  | Expr '*' Expr                           { EMul $1 $3 }
  | Expr '/' Expr                           { EDiv $1 $3 }
  | Expr '%' Expr                           { EMod $1 $3 }
  | Expr '^' Expr                           { EExp $1 $3 }

  -- other
  -- if it were up to me, i'd enforce explicit dereferencing in the style of ML
  -- https://www.cs.cmu.edu/~rwh/introsml/core/refs.htm
  | Ref                                     { ERead $1 }
  | EthEnv                                  { EEnv $1 }
  | 'if' Expr 'then' Expr 'else' Expr 'fi'  { EITE $2 $4 $6 }

EthEnv : 
    'CALLER'                                { EnvCaller }
  | 'CALLVALUE'                             { EnvCallValue }
  | 'CALLDEPTH'                             { EnvCallDepth }
  | 'ORIGIN'                                { EnvOrigin }
  | 'BLOCKHASH'                             { EnvBlockHash }
  | 'BLOCKNUMBER'                           { EnvBlockNumber }
  | 'DIFFICULTY'                            { EnvDifficulty }
  | 'CHAINID'                               { EnvChainID }
  | 'GASLIMIT'                              { EnvGasLimit }
  | 'COINBASE'                              { EnvCoinbase }
  | 'TIMESTAMP'                             { EnvTimestamp }
  | 'THIS'                                  { EnvAddress }
  | 'NONCE'                                 { EnvNonce }

{

nowhere = AlexPn 0 0 0

validsize :: Int -> Bool
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> Either String a
parseError [] = Left "parse error: empty program"
parseError ((L token posn):_) = Left $ concat
    [ "parse error: ", show token, " at ", show posn ]

}
