{
module Parse where
import Prelude hiding (EQ, GT, LT)
import Lex
import EVM.ABI
import Syntax
import Control.Monad.Except
}

%name parse
%monad { Except (AlexPosn,String } { (>>=) } { return }
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
%left '++'
%left '['
%nonassoc '%'
%left '.' -- or maybe left, not sure
%right '^'

%nonassoc '<=' '<' '>=' '>' '==' '=/='

%%

ACT : list(Behaviour)                                { $1 }


-- parameterized productions --

pair(a,b) : a b                                       { ($1,$2) }

seplist(x, sep) : {- empty -}                         { []      }
                | x                                   { [$1]    }
                | seplist(x, sep) sep x               { $3 : $1 }

nonemptysep(x, sep) : x                                   { [$1]    }
                    | seplist(x, sep) sep x               { $3 : $1 }


nonempty(x) : x                                       { [$1]    }
            | nonempty(x) x                           { $2 : $1 }

list(x) : {- empty -}                                 { []      }
        | list(x) x                                   { $2 : $1 }

opt(x) : x                                            { Just $1 }
       | {- empty -}                                  { Nothing }


-- rules --

Behaviour : Transition                                { $1 }
          | Constructor                               { $1 }

Transition : 'behaviour' id 'of' id
             Interface
             list(Precondition)
             Cases
             opt(Ensures)                             { Transition $2 $4 $5 $6 $7 $8 }

Constructor : 'behaviour' id 'of' id
              'interface' 'constructor' '(' seplist(Decl, ',') ')'
              list(Precondition)
              Creation
              list(ExtStorage)
              opt(Ensures)
              opt(Invariants)                          { Constructor $2 $4
                                                         (Interface "constructor" $8)
                                                         $10 $11 $12 $13 $14 }

Ensures : 'ensures' nonempty(Expr)                    { $2 }

Invariants : 'invariants' nonempty(Expr)              { $2 }

Interface : 'interface' id '(' seplist(Decl, ',') ')' { Interface $2 $4 }

Case : 'case' Expr ':' nonempty(Case)                 { Branch (pos $1) $2 $4 }
     | 'case' Expr ':' Post                           { Leaf (pos $1) $2 $4 }

Cases : Post                                          { TDirect $1 }
      | nonempty(Case)                                { Cases $1 }


Post  : Storage list(ExtStorage)                      { Post (Just $1) $2 Nothing }
      | list(ExtStorage) Returns                      { Post Nothing $1 (Just $2) }
      | nonempty(ExtStorage)                          { Post Nothing $1 Nothing }
      | Storage list(ExtStorage) Returns              { Post (Just $1) $2 (Just $3) }

Returns : 'returns' Expr                              { $2 }

Storage : 'storage' nonempty(Store)                   { $2 }

ExtStorage : 'storage' id nonempty(Store)             { ExtStorage $2 $3 }
           | 'creates' id 'at' Expr nonempty(Assign)  { ExtCreates $2 $4 $5 }

Precondition : 'iff' nonempty(Expr)                   { Iff (pos $1) $2 }
             | 'iff in range' Type nonempty(Expr)     { IffIn (pos $1) $2 $3 }

Store : Entry '=>' Expr                               { ($1, $3) }

Entry : id list(Zoom)                                 { Entry $1 $2 }

Zoom : '[' Expr ']'                                   { $2 }
     | '.' Expr                                       { $2 }

Creation : 'creates' nonempty(Assign)                 { Creates $2 }

Assign : StorageDecl ':=' Expr                        { AssignVal $1 $3 }
       | StorageDecl ':=' '[' seplist(Defn, ',') ']'  { AssignMany $1 $4 }

Defn : Expr ':=' Expr                                 { Defn $1 $3 }
Decl : Type id                                        { Decl $1 $2 }

StorageDecl : Container id                            { StorageDecl $1 $2 }

Type : 'uint'
       { case validsize $1 of
              True  -> AbiUIntType $1 
              False -> error "invalid uint size"
       }
     | 'int'
       { case validsize $1 of
              True  -> AbiIntType $1
              False -> error "invalid int size"
       }
     | 'bytes'                                        { AbiBytesType $1 }
     | Type '[' ilit ']'                              { AbiArrayType (fromIntegral $3) $1 }
     | 'address'                                      { AbiAddressType }
     | 'bool'                                         { AbiBoolType }
     | 'string'                                       { AbiStringType }

Container : 'mapping' '(' Type '=>' Container ')'     { Mapping $3 $5 }
          | Type                                      { Direct $1 }
Expr :

    '(' Expr ')'                                        { $2 }

  -- terminals
  | id                                                  { Var $1 }
  | ilit                                                { IntLit $1 }
  | '_'                                                 { Wild }
  -- missing string literal
  -- missing wildcard

  -- boolean expressions
  | Expr 'and' Expr                                     { EAnd  (pos $2) $1 $3 }
  | Expr 'or'  Expr                                     { EOr   (pos $2) $1 $3 }
  | Expr '=>'  Expr                                     { EImpl (pos $2) $1 $3 }
  | Expr '=='  Expr                                     { EEq   (pos $2) $1 $3 }
  | Expr '=/=' Expr                                     { ENeq  (pos $2) $1 $3 }
  | Expr '<='  Expr                                     { ELEQ  (pos $2) $1 $3 }
  | Expr '<'   Expr                                     { ELT   (pos $2) $1 $3 }
  | Expr '>='  Expr                                     { EGEQ  (pos $2) $1 $3 }
  | Expr '>'   Expr                                     { EGT   (pos $2) $1 $3 }
  | 'true'                                              { ETrue (pos $1) }
  | 'false'                                             { EFalse (pos $1) }

  -- integer expressions
  | Expr '+'   Expr                                     { EAdd (pos $2)  $1 $3 }
  | Expr '-'   Expr                                     { ESub (pos $2)  $1 $3 }
  | Expr '*'   Expr                                     { EMul (pos $2)  $1 $3 }
  | Expr '/'   Expr                                     { EDiv (pos $2)  $1 $3 }
  | Expr '%'   Expr                                     { EMod (pos $2)  $1 $3 }
  | Expr '^'   Expr                                     { EExp (pos $2)  $1 $3 }

  -- composites
  | 'if' Expr 'then' Expr 'else' Expr                   { EITE (pos $1) $2 $4 $6 }
  | Expr '[' Expr ']'                                   { Look (pos $2) $1 $3 }
  | Expr '.' Expr                                       { Zoom (pos $2) $1 $3 }
--  | id '(' seplist(Expr, ',') ')'                     { App    (pos $1) $1 $3 }
  | Expr '++' Expr                                      { ECat   (pos $2) $1 $3 }
--  | id '[' Expr '..' Expr ']'                         { ESlice (pos $2) $1 $3 $5 }
  -- missing builtins
  | 'newAddr' '(' Expr ',' Expr ')'                     { Newaddr (pos $1) $3 $5 }
{

validsize :: Int -> Bool
validsize x = (mod x 8 == 0) && (x >= 8) && (x <= 256)

parseError :: [Lexeme] -> Except (AlexPosn,String) arror
parseError [] = throwError (AlexPn 0 0 0, "no valid tokens")
parseError ((L token posn):tokens) =
  throwError $ (posn, concat [
    "parse error on ",
    show token,
    " at ",
    showposn posn])
}
