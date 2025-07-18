.PHONY: verify
verify: RocqMakefile Exponent.v
	make -f RocqMakefile

Exponent.v: exponent.act
	act coq --file exponent.act > Exponent.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f Exponent.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
