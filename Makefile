.DEFAULT_GOAL := compiler
.PHONY: parser compiler

parser: src/parser.timestamp

# generates the haskell files that do parsing (compiler compiler)
src/parser.timestamp: src/act.cf
	cd src && make parser && cd ..

# builds the rest of the haskell files (compiler)
compiler: parser
	cd src && cabal v2-build && cd ..

test_specs=$(wildcard tests/*/*.act)

test-parser: parser $(test_specs:=.parse)

# Just checks parsing
tests/%.parse:
	./src/haskell/TestAct tests/$*

test-compiler: compiler $(test_specs:=.compile)

