.PHONY: verify
verify: RocqMakefile ERC20.v
	make -f RocqMakefile

ERC20.v: erc20.act
	act coq --file erc20.act > ERC20.v

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

.PHONY: clean
clean:
	if [[ -f RocqMakefile ]]; then make -f RocqMakefile clean; fi
	rm -f ERC20.v RocqMakefile RocqMakefile.conf
	rm -f *.glob *.vo *.vok *.vos
