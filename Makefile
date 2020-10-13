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

# supposed to pass, but don't
hevm_buggy=tests/hevm/pass/safemath/safemath.act tests/hevm/pass/transfer/transfer.act
# supposed to pass
hevm_pass=$(filter-out $(hevm_buggy), $(wildcard tests/hevm/pass/*/*.act))
# supposed to fail
hevm_fail=$(wildcard tests/hevm/fail/*/*.act)

failing_typing=tests/frontend/array/array.act tests/frontend/dss/vat.act tests/frontend/creation/createMultiple.act

coq-examples = tests/coq/transitions tests/coq/safemath tests/coq/exponent

.PHONY: test-coq $(coq-examples)
test-coq: compiler $(coq-examples)
$(coq-examples):
	make -C $@

test-parse: parser compiler $(parser_specs:=.parse)
test-type: parser compiler $(typing_specs:=.type)
test-invariant: parser compiler $(invariant_pass:=.invariant.pass) $(invariant_fail:=.invariant.fail)
test-hevm: parser compiler $(hevm_pass:=.hevm.pass) $(hevm_fail:=.hevm.fail)


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

tests/hevm/pass/%.act.hevm.pass:
	solc --combined-json=bin,bin-runtime,ast,metadata,abi,srcmap,srcmap-runtime,storage-layout tests/hevm/pass/$*.sol > tests/hevm/pass/$*.sol.json
	./bin/act hevm --spec tests/hevm/pass/$*.act --soljson tests/hevm/pass/$*.sol.json
	rm tests/hevm/pass/$*.sol.json

tests/hevm/fail/%.act.hevm.fail:
	solc --combined-json=bin,bin-runtime,ast,metadata,abi,srcmap,srcmap-runtime,storage-layout tests/hevm/fail/$*.sol > tests/hevm/fail/$*.sol.json
	./bin/act hevm --spec tests/hevm/fail/$*.act --soljson tests/hevm/fail/$*.sol.json && exit 1 || echo 0
	rm tests/hevm/fail/$*.sol.json

test: test-parse test-type test-invariant test-coq test-hevm
