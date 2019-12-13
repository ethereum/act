#src/act.cf: 

build-hs: ./src/act.cf
	bnfc -m --haskell src/act.cf -o src/haskell && cd src/haskell && make

test_specs=$(wildcard tests/*/*.act)

test-parse: build-hs $(test_specs:=.parse)

# Just checks parsing
tests/%.parse:
	./src/haskell/TestAct tests/$*
