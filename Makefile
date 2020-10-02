.DEFAULT_GOAL := compiler
.PHONY: parser compiler

parser: src/Lex.hs src/Parse.hs

src/Parse.hs: src/Parse.y src/Syntax.hs
	happy src/Parse.y


src/Lex.hs: src/Lex.x
	alex src/Lex.x

# builds the rest of the haskell files (compiler)
bin/act: src/*.hs
	cd src && cabal v2-install --installdir=../bin --overwrite-policy=always && cd ..

repl: src/Lex.hs src/Parse.hs
	cd src && cabal v2-repl

compiler: bin/act

test_specs=$(wildcard tests/*/*.act)

parser_specs=$(filter-out $(invariant_specs), $(test_specs))
typing_specs=$(filter-out $(failing_typing), $(parser_specs))

invariant_specs=$(wildcard tests/invariants/*/*.act)
invariant_pass=$(wildcard tests/invariants/pass/*.act) $(typing_specs)
invariant_fail=$(wildcard tests/invariants/fail/*.act)

failing_typing=tests/array/array.act tests/dss/vat.act tests/creation/createMultiple.act

test-parse: parser compiler $(parser_specs:=.parse)
test-type: parser compiler $(typing_specs:=.type)
test-invariant: parser compiler $(invariant_pass:=.invariant.pass) $(invariant_fail:=.invariant.fail)

# Just checks parsing
tests/%.parse:
	./bin/act parse --file tests/$* > tests/$*.parsed.hs.out
	diff tests/$*.parsed.hs.out tests/$*.parsed.hs
	rm tests/$*.parsed.hs.out

tests/%.type:
	./bin/act type --file tests/$* | jq . > tests/$*.typed.json.out
	diff tests/$*.typed.json.out tests/$*.typed.json
	rm tests/$*.typed.json.out

tests/%.invariant.pass:
	./bin/act prove --file tests/$*
	./bin/act prove --solver cvc4 --file tests/$*

tests/%.invariant.fail:
	./bin/act prove --file tests/$* && exit 1 || echo 0
	./bin/act prove --solver cvc4 --file tests/$* && exit 1 || echo 0

test: test-parse test-type test-invariant
