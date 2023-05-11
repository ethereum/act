.PHONY: verify
verify: CoqMakefile Multi.v
	make -f CoqMakefile

Multi.v: multi.act
	act coq --file multi.act > Multi.v

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: clean
clean:
	if [[ -f CoqMakefile ]]; then make -f CoqMakefile clean; fi
	rm -f Exponent.v CoqMakefile CoqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
