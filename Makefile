.DEFAULT_GOAL := compiler
.PHONY: parser compiler

parser: src/Lex.hs src/Parse.hs

src/Parse.hs: src/Parse.y src/Syntax.hs
	happy src/Parse.y


src/Lex.hs: src/Lex.x
	alex src/Lex.x

# builds the rest of the haskell files (compiler)
bin/act: src/Lex.hs src/Parse.hs src/Main.hs
	cd src && cabal v2-install --installdir=../bin --overwrite-policy=always && cd ..

repl: src/Lex.hs src/Parse.hs
	cd src && cabal v2-repl

compiler: bin/act

test_specs=$(wildcard tests/*/*.act)

test-parse: parser compiler $(test_specs:=.parse)

# Just checks parsing
tests/%.parse:
	./bin/act parse --file tests/$* > tests/$*.parsed.hs.out
	diff tests/$*.parsed.hs.out tests/$*.parsed.hs
	rm tests/$*.parsed.hs.out

test-compiler: compiler $(test_specs:=.compile)

