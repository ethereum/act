SafeMath.vo Theory.vo: CoqMakefile SafeMath.v Theory.v
	make -f CoqMakefile

SafeMath.v: safemath.act
	act coq --file safemath.act > SafeMath.v

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: clean
clean:
	if [[ -f CoqMakefile ]]; then make -f CoqMakefile clean; fi
	rm -f SafeMath.v CoqMakefile CoqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
