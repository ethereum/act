.PHONY: verify
verify: RocqMakefile Multi.v
	make -f RocqMakefile

Multi.v: multi.act
	act coq --file multi.act > Multi.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f Multi.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
