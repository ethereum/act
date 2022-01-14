# Hevm Decompilation Pipeline / Bytecode Verification V2

The existing bytecode verification pipeline (`act hevm`) is severly underpowered and is currently
unable to verify even extremely trivial contracts (e.g. safemath). The main problem here is the
mismatch between the numeric representations used in hevm and act. Act uses unbounded integers,
whereas hevm makes use of wrapping bitvectors. An equivalence proof between a given bytecode object
and a set of act specifications must therefore translate between these two representations, this is
currently achieved using the `int_to_bv` and `bv_to_int` smt operations. These operations appear to
be very hard on the solver and cause the above mentioned lack of verification power.

This document outlines a design for a new bytecode verification pipeline that runs as follows:

1. Decompile evm bytecode into an act AST
1. Apply various normalisation & simplification passes against the act AST
1. Run an SMT based equivalence checking routine between the user provided act spec and the decompiled act spec

The above approach should have several benefits:

- Abstraction from EVM into a higher level AST should simplify automated reasoning
- Application of syntactic simplification & rewriting rules should make life easier for the solvers
- Modularization & decomposition of the problem should allow us to produce simpler SMT, once again making life easier for the solvers
- The decompilation pipeline can be used to automatically generate act specs, automating much of the boilerplate generation
- User defined rewrite rules could allow for a semi-automated approach, expanding the scope of programs that can be verified

## Design Sketch

Two new act commands:

- `act decompile output.json`: outputs an act spec for a given bytecode object, uses nice human readable names if provided with solidity compiler output
- `act equivalence spec1 spec2`: checks if the two specs are equivalent, shows a counterexample if they are not

### Decompilation Pipeline

#### 1. Extract EVM AST

We begin by performing a full symbolic execution of the target contract. At this point we do not run
any reachability analysis, and the resulting execution tree contains all code paths present in the
bytecode, including ones that can never be reached. This lets us avoid calling out to SMT in this
stage.

#### 2. Remove Bitvector Ops

1. All bitvector arithmetic operations are replaced with integer arithmetic mod uint256
1. Strip mods: we walk the execution tree and run an SMT query on each arithmetic op to see if it
   can actually overflow (this should only be possible for unchecked blocks), if overflow cannot
   happen there we can safely strip the mod. It may even be possible to skip SMT entirely here, and
   just pattern match on known safemath routines. Alterntively we can maybe simplify the SMT queries
   by only checking a subset of the path conditions prior to the arithmetic op (as only the pcs
   involved in the safemath checking are actually relevant to being able to strip the mod).

#### 3. Convert to Act

1. Remove all reverting branches from the AST
1. Split into multiple ASTs based on function selectors
1. Populate an act behaviour for each branch in each subtree. Path conditions are set as preconditions, and storage rewrites are inserted
1. Run term rewriting & simplification engine on every behv
1. Check reachability: Ask smt if the preconditions for each behv are satisfiable, discard if they aren't

### Equivalence Checking

The following is a pretty simplistic approach that relies fairly heavily on SMT. It is intended as
an MVP approach to equivalence checking for act specs, more refined approaches may be required to
achieve the performance that we desire. It may also be possible to directly export problematic
queries into a theorem prover for manual proof if required.

A behaviour can be represented as an implication with the preconditions on the lhs and the storage
rewrites on the rhs. Given two specs (A & B) we can gather all behaviours from each spec that share
the same interface.

We can run a quick check to ensure that there is at least one behaviour from both spec A and spec B
for all interfaces present in both specs. A failure here is an obvious equivalence break.

If the above is satisfied, we can run the following routine for each group of behaviours:

For each behaviour from spec A we can construct an SMT query that looks something like the following:

```smt
<Declare Calldata Variables>
<Declare Storage Prestate Vars>
<Declare Storage Poststate Vars>

<Assert implications for every behaviour in spec B>

<Assert preconditions from spec A behv>
<Assert negation of storage rewrites from spec A behv>

(check-sat)
```

If we get `unsat` for all behaviours in spec A then we have a proof that all behaviours in spec A
are implemented by spec B.

In order to prove that spec B does not implement any additional behaviours we can run the following
query

```smt
<Declare Calldata Variables>
<Declare Storage Prestate Vars>
<Declare Storage Poststate Vars>

<Assert implications for every behaviour in spec B>

<Assert negation of the conjuction of preconditions from all behaviours in spec A>
<Assert disjunction of the storage rewrites for all behvs in spec B>

(check-sat)
```

An `unsat` result here shows that there are no storage rewrites from the behaviours in spec B
that can be reached without satisfying the preconditions from a behaviour in spec A (which we
already know are all implemented by the behaviours in spec B), implying that spec B does not
implement any additional behaviour outside of that defined in spec A.

## Open Questions

- What degree of certification is desirable? Should the decompilation pass be certified? Can we
    attach a proof to manual rewrites? Is there a way we can leverage a theorem prover here, perhaps
    rewrites can be extracted from Coq?

- Do we actually need an intermediate spec language (act) at all? Can we just export directly to a
    theorem prover and prove properties there?

- At what level do we want to run the term rewriting engine? Against the EVM level AST, or against
    the act AST?
