.PHONY: verify
verify: CoqMakefile ERC20.v
	make -f CoqMakefile

ERC20.v: erc20.act
	act coq --file erc20.act > ERC20.v

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: clean
clean:
	if [[ -f CoqMakefile ]]; then make -f CoqMakefile clean; fi
	rm -f StateMachine.v CoqMakefile CoqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
