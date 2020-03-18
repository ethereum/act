.DEFAULT_GOAL := compiler
.PHONY: parser compiler

parser: src/parser.timestamp

# generates the haskell files that do parsing (compiler compiler)
src/parser.timestamp: src/act.cf
	cd src && make parser && cd ..

# builds the rest of the haskell files (compiler)
bin/act: src/parser.timestamp src/Main.hs
	cd src && cabal v2-install --installdir=../bin --overwrite-policy=always && cd ..

repl: src/parser.timestamp
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

