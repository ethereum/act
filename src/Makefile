main: Lex.hs Parse.hs 

Parse.hs: Parse.y
	happy Parse.y

Lex.hs: Lex.x
	alex Lex.x

.PHONY: clean
clean:
	rm -f *.hi *.o Lex.hs Parse.hs main
