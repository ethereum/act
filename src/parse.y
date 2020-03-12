{
module Main where
import Lex
}

%name parse
%tokentype { Token }
%error { parseError }

%token 
      'behaviour'             { BEHAVIOUR _ }
      OF                    { OF _ }
      INTERFACE             { INTERFACE _ }
      id                    { ID _ _ }
      '('                   { LPAREN _ }
      ')'                   { RPAREN _ }

%%

B : 'behaviour' id OF id      { () } -- tmp

{

parseError :: [Token] -> a
parseError _ = error "Parse error"

main = do
  contents <- getContents
  let tree = parse $ alexScanTokens contents
  print tree
  -- putStrLn "hi"
}