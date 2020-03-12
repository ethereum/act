{
module Lex (Token (..), alexScanTokens) where
import Prelude hiding (EQ, GT, LT)
}

%wrapper "posn"

$digit = 0-9                    -- digits
$alpha = [a-z A-Z]              -- alphabetic characters
$ident = [$alpha _]

tokens :-

  $white+                               ;

  -- reserved words
  behaviour                             { \ p s -> BEHAVIOUR p }
  of                                    { \ p s -> OF p }
  interface                             { \ p s -> INTERFACE p }
  constructor                           { \ p s -> CONSTRUCTOR p }
  creates                               { \ p s -> CREATES p }
  case                                  { \ p s -> CASE p }
  returns                               { \ p s -> RETURNS p }
  storage                               { \ p s -> STORAGE p }
  noop                                  { \ p s -> NOOP p }
  "iff in range"                        { \ p s -> IFFINRANGE p }
  iff                                   { \ p s -> IF p }
  and                                   { \ p s -> AND p }
  or                                    { \ p s -> OR p }
  true                                  { \ p s -> TRUE p }
  false                                 { \ p s -> FALSE p }

  -- builtin types
  uint                                  { \ p s -> UINT p }
  int                                   { \ p s -> INT p }
  string                                { \ p s -> STRING p }
  address                               { \ p s -> ADDRESS p }
  bytes                                 { \ p s -> BYTES p }

  -- symbols
  ":="                                  { \ p s -> ASSIGN p }
  "->"                                  { \ p s -> ARROW p }
  "=>"                                  { \ p s -> ARROW' p }
  "=="                                  { \ p s -> EQEQ p }
  "=/="                                 { \ p s -> NEQ p }
  ">="                                  { \ p s -> GE p }
  "<="                                  { \ p s -> LE p }
  "++"                                  { \ p s -> CAT p }
  ".."                                  { \ p s -> SLICE p }
  "("                                   { \ p s -> LPAREN p }
  ")"                                   { \ p s -> RPAREN p }
  "["                                   { \ p s -> LBRACK p }
  "]"                                   { \ p s -> RBRACK p }
  "="                                   { \ p s -> EQ p }
  ">"                                   { \ p s -> GT p }
  "<"                                   { \ p s -> LT p }
  ":"                                   { \ p s -> COLON p }
  "+"                                   { \ p s -> PLUS p }
  "-"                                   { \ p s -> MINUS p }
  "*"                                   { \ p s -> STAR p }
  "/"                                   { \ p s -> SLASH p }
  "%"                                   { \ p s -> MOD p }
  "^"                                   { \ p s -> CARROT p }
  "_"                                   { \ p s -> SCORE p }
  "."                                   { \ p s -> DOT p }
  ","                                   { \ p s -> COMMA p }

  -- identifiers
  $ident ($ident | $digit)*   { \ p s -> ID p s }

  -- literals
  $digit+                     { \ p s -> LIT p (read s) }

{

type P = AlexPosn

data Token =

  -- reserved words
    BEHAVIOUR P
  | OF        P
  | INTERFACE P
  | CONSTRUCTOR P
  | CREATES P
  | CASE P
  | RETURNS P
  | STORAGE P
  | NOOP P
  | IFFINRANGE P
  | IF P
  | AND P
  | OR P
  | TRUE P
  | FALSE P

  -- builtin types
  | UINT P
  | INT P
  | ADDRESS P
  | STRING P
  | BYTES P

  -- symbols
  | ASSIGN P
  | ARROW P
  | ARROW' P
  | EQEQ P
  | NEQ P
  | GE P
  | LE P
  | CAT P
  | SLICE P
  | LPAREN P
  | RPAREN P
  | LBRACK P
  | RBRACK P
  | EQ P
  | GT P
  | LT P
  | COLON P
  | PLUS P
  | MINUS P
  | STAR P
  | SLASH P
  | MOD P
  | CARROT P
  | SCORE P
  | DOT P
  | COMMA P

  -- identifiers
  | ID P String

  -- literals
  | LIT P Integer
  deriving (Eq,Show)
}
