.PHONY: verify
verify: CoqMakefile Exponent.v
	make -f CoqMakefile

Exponent.v: exponent.act
	act coq --file exponent.act > Exponent.v

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: clean
clean:
	if [[ -f CoqMakefile ]]; then make -f CoqMakefile clean; fi
	rm -f Exponent.v CoqMakefile CoqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
