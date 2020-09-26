StateMachine.vo Theory.vo: CoqMakefile StateMachine.v Theory.v
	make -f CoqMakefile

StateMachine.v: state_machine.act
	act coq --file state_machine.act > StateMachine.v

ActLib.v: ../../lib/ActLib.v
	cp ../../lib/ActLib.v ./

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: clean
clean:
	if [[ -f CoqMakefile ]]; then make -f CoqMakefile clean; fi
	rm -f StateMachine.v CoqMakefile CoqMakefile.conf
