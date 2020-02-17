.DEFAULT_GOAL := compiler
BUILD_DIR     := out
.PHONY: parser compiler

parser: $(BUILD_DIR)/parser.timestamp

# generates the haskell files that do parsing (compiler compiler)
$(BUILD_DIR)/parser.timestamp: src/act.cf
	bnfc -m --haskell src/act.cf -o out/parser
	touch out/parser.timestamp

# builds the rest of the haskell files (compiler)
compiler: parser
	cd src/ && cabal --enable-nix new-build --builddir=out && cd ..

test_specs=$(wildcard tests/*/*.act)

test-parser: parser $(test_specs:=.parse)

# Just checks parsing
tests/%.parse:
	./src/haskell/TestAct tests/$*

test-compiler: compiler $(test_specs:=.compile)

