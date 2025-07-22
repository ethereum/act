.PHONY: verify
verify: RocqMakefile Token.v
	make -f RocqMakefile

Token.v: token.act
	act coq --file token.act > Token.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f Token.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
