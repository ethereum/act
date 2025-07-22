.PHONY: verify
verify: RocqMakefile SafeMath.v
	make -f RocqMakefile

SafeMath.v: safemath.act
	act coq --file safemath.act > SafeMath.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f SafeMath.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
