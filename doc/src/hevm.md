# Hevm

Act leverages the symbolic execution engine in hevm to provide a backend that can prove equivalence
between a contract specification and an implementation of that specification in EVM.

## Usage

To perform the equivalence proofs, you can simply run
```sh
act hevm --spec <PATH_TO_SPEC> --sol <PATH_TO_SOLIDITY_CODE>
```
 against your spec and runtime (solidity) code.

`act hevm` also accepts the following configuration flags:

- `--code TEXT`: runtime code.
- `--initcode TEXT`: initial code.
- `--solver`: you can choose to use `cvc5` or `z3` as the solver backend. The default is `cvc5`.
  Sometimes `cvc5` may be able to prove things that `z3` cannot (and vice versa). You can also
  prove the same properties with multiple solvers to gain confidence that the proofs are not
  affected by a bug in the solver itself.
- `--smttimeout`: the timeout (in milliseconds) given for each smt query. This is set to 20000 by default.
- `--debug`: this prints the raw query dispatched to the SMT solver to stdout.

## Description

Two claims are generated for each behaviour, Pass and Fail. The Pass claim states that if all
preconditions in the iff block are true, then all executions will succeed, storage will be updated
according to the storage block, and the specified return value will, in fact, be returned. The Fail
claim states that should any of the preconditions be false, all executions will revert.

In both cases we begin the proof by constraining calldata to be of the form specified in the
behaviours’ interface blocks, as well as making the relevant assumptions depending on whether the
claim is Pass or Fail, and then symbolically executing the bytecode object with storage held to be
completely abstract.

This produces a tree of potential executions where each node represents a potential branching point,
and each leaf represents a possible final state of the contract after the execution of a single
call.

In the case of a Fail claim, we can then check that each leaf represents a state in which execution
has reverted, while for a Pass claim we can check that storage has been updated as expected, and
that the contents of the return buffer matches what was specified in the behaviour’s returns block.

## Example

As an example, consider the following contract:

```
contract Simple {
    uint val;

    function set(uint x) external payable returns (uint) {
        require(x > 100);
        val = x;
        return x;
    }
}
```

We can represent this in Act as:

```
constructor of Simple
interface constructor()

creates

  uint val := 0
behaviour set of Simple
interface set(uint x)

iff

  x > 100

storage

  val => x

returns x
```

Act needs to have access to the storage layout metadata output by solc to compute the index in storage for each variable mentioned in the spec, so we need to pass a solc output json when trying to prove equivalence.

```
> act hevm --spec src/simple.act --soljson out/dapp.sol.json
checking postcondition...
Q.E.D.
Successfully proved set(Pass), 2 cases.
checking postcondition...
Q.E.D.
Successfully proved set(Fail), 2 cases.
==== SUCCESS ====
All behaviours implemented as specified ∎.
```

If we try to prove equivalence of the spec and a faulty implementation like the one below:

```solidity
contract Simple {
    uint val;

    function set(uint x) external payable returns (uint) {
        require(x > 100);
        if (x == 2000) {
          val = x + 1;
        } else {
          val = x;
        }
        return x;
    }
}
```

Then Act will give us a counterexample showing a case where the implementation differs from the specification:

```
> act hevm --spec src/simple.act --soljson out/dapp.sol.json
checking postcondition...
Calldata:
0x60fe47b100000000000000000000000000000000000000000000000000000000000007d0
Caller:
0x0000000000000000000000000000000000000000
Callvalue:
0
Failed to prove set(Pass)
checking postcondition...
Q.E.D.
Successfully proved set(Fail), 2 cases.
==== FAILURE ====
1 out of 2 claims unproven:

1	Failed to prove set(Pass)
```
