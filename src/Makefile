main: lex.hs parse.hs syntax.hs
	ghc -o main syntax.hs parse.hs lex.hs 

parse.hs: parse.y
	happy parse.y

lex.hs: lex.x
	alex lex.x

.PHONY: clean
clean:
	rm -f *.hi *.o lex.hs parse.hs main
