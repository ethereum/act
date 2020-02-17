.DEFAULT_GOAL := compiler
.PHONY: parser compiler

parser: parser.timestamp

# generates the haskell files that do parsing (compiler compiler)
parser.timestamp: src/act.cf
	mkdir src/parser && bnfc -m --haskell src/act.cf -o src/parser
	touch parser.timestamp

# builds the rest of the haskell files (compiler)
compiler: parser
	cd src && cabal v2-build --config-file=$OUT --builddir=$OUT && cd ..

test_specs=$(wildcard tests/*/*.act)

test-parser: parser $(test_specs:=.parse)

# Just checks parsing
tests/%.parse:
	./src/haskell/TestAct tests/$*

test-compiler: compiler $(test_specs:=.compile)

