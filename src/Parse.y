{
module Parse where
import Prelude hiding (EQ, GT, LT)
import Lex
import EVM.ABI
import EVM.Solidity (SlotType(..))
import qualified Data.List.NonEmpty as NonEmpty
import Syntax
import ErrM
}

%name parse
%monad { Err } { (>>=) } { return }
%tokentype { Lexeme }
%error { parseError }

%token

  -- reserved word
  'constructor'               { L CONSTRUCTOR _ }
  'behaviour'                 { L BEHAVIOUR _ }
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
  'not'                       { L NOT _ }
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

%nonassoc '[' ']' '.'

-- boolean
%nonassoc '=>'
%left 'and' 'or'
%nonassoc 'not'
%left '==' '=/='
%nonassoc '<=' '<' '>=' '>'

-- numeric
%left '+' '-'
%left '*' '/'
%nonassoc '%'
%left '^'

-- bytestrings
%left '++'

%%

ACT : list(Behaviour)                                { $1 }


-- parameterized productions --

pair(a,b) : a b                                       { ($1,$2) }

seplist(x, sep) : {- empty -}                         { []      }
                | x                                   { [$1]    }
                | x sep seplist(x, sep)               { $1 : $3 }

nonempty(x) : x                                       { [$1]    }
            | x nonempty(x)                           { $1 : $2 }

list(x) : {- empty -}                                 { []      }
        | x list(x)                                   { $1 : $2 }

optblock(label, x) : label nonempty(x)                { $2 }
                   | {- empty -}                      { [] }

-- rules --

Behaviour : Transition                                { $1 }
          | Constructor                               { $1 }

Transition : 'behaviour' id 'of' id
             Interface
             list(Precondition)
             Cases
             Ensures                                  { Transition (name $2) (name $4)
                                                        $5 $6 $7 $8 }

Constructor : 'constructor' 'of' id
              CInterface
              list(Precondition)
              Creation
              list(ExtStorage)
              Ensures
              Invariants                              { Definition (name $3)
                                                         $4 $5 $6 $7 $8 $9 }

Ensures : optblock('ensures', Expr)                   { $1 }

Invariants : optblock('invariants', Expr)             { $1 }

Interface : 'interface' id '(' seplist(Decl, ',') ')' { Interface (name $2) $4 }

CInterface : 'interface' 'constructor' '(' seplist(Decl, ',') ')' { Interface "constructor" $4 }

Cases : Post                                          { Direct $1 }
      | nonempty(Case)                                { Branches $1 }

Case : 'case' Expr ':' Post                           { Case (posn $1) $2 $4 }


Post  : Storage list(ExtStorage)                      { Post (Just $1) $2 Nothing }
      | list(ExtStorage) Returns                      { Post Nothing $1 (Just $2) }
      | nonempty(ExtStorage)                          { Post Nothing $1 Nothing }
      | Storage list(ExtStorage) Returns              { Post (Just $1) $2 (Just $3) }

Returns : 'returns' Expr                              { $2 }

Storage : 'storage' nonempty(Store)                   { $2 }

ExtStorage : 'storage' id nonempty(Store)             { ExtStorage (name $2) $3 }
           | 'creates' id 'at' Expr nonempty(Assign)  { ExtCreates (name $2) $4 $5 }
           | 'storage' '_' '_' '=>' '_'               { WildStorage }

Precondition : 'iff' nonempty(Expr)                   { Iff (posn $1) $2 }
             | 'iff in range' Type nonempty(Expr)     { IffIn (posn $1) $2 $3 }

Store : Entry '=>' Expr                               { Rewrite $1 $3 }
      | Entry                                         { Constant $1 }

Entry : id list(Zoom)                                 { Entry (posn $1) (name $1) $2 }
      | '_'                                           { Wild }

Zoom : '[' Expr ']'                                   { $2 }
     | '.' Expr                                       { $2 }

Creation : 'creates' list(Assign)                     { Creates $2 }

Assign : StorageVar ':=' Expr                        { AssignVal $1 $3 }
       | StorageVar ':=' '[' seplist(Defn, ',') ']'  { AssignMany $1 $4 }

Defn : Expr ':=' Expr                                 { Defn $1 $3 }
Decl : Type id                                        { Decl $1 (name $2) }

StorageVar : SlotType id                            { StorageVar $1 (name $2) }

Type : 'uint'
       { case validsize $1 of
              True  -> AbiUIntType $1
              False -> error $ "invalid uint size: uint" <> (show $1)
       }
     | 'int'
       { case validsize $1 of
              True  -> AbiIntType $1
              False -> error $ "invalid int size: int" <> (show $1)
       }
     | 'bytes'                                        { AbiBytesType $1 }
     | Type '[' ilit ']'                              { AbiArrayType (fromIntegral $ value $3) $1 }
     | 'address'                                      { AbiAddressType }
     | 'bool'                                         { AbiBoolType }
     | 'string'                                       { AbiStringType }

SlotType : 'mapping' '(' MappingArgs ')'             { (uncurry StorageMapping) $3 }
         | Type                                      { StorageValue $1 }


MappingArgs : Type '=>' Type                           { ($1 NonEmpty.:| [], $3) }
            | Type '=>' 'mapping' '(' MappingArgs ')'  { (NonEmpty.cons $1 (fst $5), snd $5)  }

Expr : '(' Expr ')'                                    { $2 }

  -- terminals
  | ilit                                                { IntLit (posn $1) (value $1) }
  | '_'                                                 { WildExp (posn $1) }
  -- missing string literal
  -- missing wildcard

  -- boolean expressions
  | Expr 'and' Expr                                     { EAnd  (posn $2) $1 $3 }
  | Expr 'or'  Expr                                     { EOr   (posn $2) $1 $3 }
  | Expr '=>'  Expr                                     { EImpl (posn $2) $1 $3 }
  | 'not'      Expr                                     { ENot  (posn $1) $2 }
  | Expr '=='  Expr                                     { EEq   (posn $2) $1 $3 }
  | Expr '=/=' Expr                                     { ENeq  (posn $2) $1 $3 }
  | Expr '<='  Expr                                     { ELEQ  (posn $2) $1 $3 }
  | Expr '<'   Expr                                     { ELT   (posn $2) $1 $3 }
  | Expr '>='  Expr                                     { EGEQ  (posn $2) $1 $3 }
  | Expr '>'   Expr                                     { EGT   (posn $2) $1 $3 }
  | 'true'                                              { BoolLit (posn $1) True }
  | 'false'                                             { BoolLit (posn $1) False }

  -- integer expressions
  | Expr '+'   Expr                                     { EAdd (posn $2)  $1 $3 }
  | Expr '-'   Expr                                     { ESub (posn $2)  $1 $3 }
  | Expr '*'   Expr                                     { EMul (posn $2)  $1 $3 }
  | Expr '/'   Expr                                     { EDiv (posn $2)  $1 $3 }
  | Expr '%'   Expr                                     { EMod (posn $2)  $1 $3 }
  | Expr '^'   Expr                                     { EExp (posn $2)  $1 $3 }

  -- composites
  | 'if' Expr 'then' Expr 'else' Expr                   { EITE (posn $1) $2 $4 $6 }
  | id list(Zoom)                                       { EntryExp (posn $1) (name $1) $2 }
--  | id list(Zoom)                                       { Look (posn $1) (name $1) $2 }
  | Expr '.' Expr                                       { Zoom (posn $2) $1 $3 }
--  | id '(' seplist(Expr, ',') ')'                     { App    (posn $1) $1 $3 }
  | Expr '++' Expr                                      { ECat   (posn $2) $1 $3 }
--  | id '[' Expr '..' Expr ']'                         { ESlice (posn $2) $1 $3 $5 }
  | 'CALLER'                                            { EnvExp (posn $1) Caller }
  | 'CALLDEPTH'                                         { EnvExp (posn $1) Calldepth }
  | 'ORIGIN'                                            { EnvExp (posn $1) Origin }
  | 'BLOCKHASH'                                         { EnvExp (posn $1) Blockhash }
  | 'BLOCKNUMBER'                                       { EnvExp (posn $1) Blocknumber }
  | 'DIFFICULTY'                                        { EnvExp (posn $1) Difficulty }
  | 'CHAINID'                                           { EnvExp (posn $1) Chainid }
  | 'GASLIMIT'                                          { EnvExp (posn $1) Gaslimit }
  | 'COINBASE'                                          { EnvExp (posn $1) Coinbase }
  | 'TIMESTAMP'                                         { EnvExp (posn $1) Timestamp }
  | 'CALLVALUE'                                         { EnvExp (posn $1) Callvalue }
  | 'THIS'                                              { EnvExp (posn $1) This }
  | 'NONCE'                                             { EnvExp (posn $1) Nonce }
  -- missing builtins
  | 'newAddr' '(' Expr ',' Expr ')'                     { ENewaddr (posn $1) $3 $5 }

{

nowhere = AlexPn 0 0 0
lastPos = AlexPn (-1) (-1) (-1)

validsize :: Int -> Bool
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> Err a
parseError [] = Bad (lastPos, "Expected more tokens")
parseError ((L token pn):_) =
  Bad $ (pn, concat [
    "parsing error at token ",
    show token])
}
