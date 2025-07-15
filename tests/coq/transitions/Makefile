.PHONY: verify
verify: RocqMakefile StateMachine.v
	make -f RocqMakefile

StateMachine.v: state_machine.act
	act coq --file state_machine.act > StateMachine.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f StateMachine.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
