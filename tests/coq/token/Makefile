.PHONY: verify
verify: CoqMakefile Token.v
	make -f CoqMakefile

Token.v: token.act
	act coq --file token.act > Token.v

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: clean
clean:
	if [[ -f CoqMakefile ]]; then make -f CoqMakefile clean; fi
	rm -f StateMachine.v CoqMakefile CoqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
