.PHONY: verify
verify: CoqMakefile StateMachine.v
	make -f CoqMakefile

StateMachine.v: state_machine.act
	act coq --file state_machine.act > StateMachine.v

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: clean
clean:
	if [[ -f CoqMakefile ]]; then make -f CoqMakefile clean; fi
	rm -f StateMachine.v CoqMakefile CoqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
