main: lex.hs parse.hs Syntax.hs
	ghc -o main Syntax.hs parse.hs lex.hs 

parse.hs: parse.y
	happy parse.y

lex.hs: lex.x
	alex lex.x

.PHONY: clean
clean:
	rm -f *.hi *.o lex.hs parse.hs main
